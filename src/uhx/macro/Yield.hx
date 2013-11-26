package uhx.macro;

import haxe.macro.Type;
import haxe.macro.Expr;
import haxe.macro.Context;
import uhx.macro.klas.Handler;

using uhu.macro.Jumla;
using haxe.macro.ExprTools;

/**
 * ...
 * @author Skial Bainn
 */
class Yield {

	private static function initialize() {
		try {
			if (!Handler.setup) {
				Handler.initalize();
			}
			
			Handler.DEFAULTS.push(Yield.handler);
		} catch (e:Dynamic) {
			// This assumes that `implements Klas` is not being used
			// but `@:autoBuild` or `@:build` metadata is being used 
			// with the provided `uhx.macro.Yield.build()` method.
		}
	}
	
	public static function build():Array<Field> {
		return handler( Context.getLocalClass().get(), Context.getBuildFields() );
	}
	
	public static var cls:ClassType = null;
	
	public static function handler(cls:ClassType, fields:Array<Field>):Array<Field> {
		Yield.cls = cls;
		
		if (!Context.defined( 'display' )) for (field in fields) switch (field.kind) {
			case FFun(method) if (method.expr != null):
				finalize( loop( method.expr, field.name ), method );
				
			case _:
		}
		
		return fields;
	}
	
	public static var name:String = null;
	public static var cases:Array<Expr> = null;
	public static var counter:Int = 0;
	
	public static function loop(e:Expr, n:String, ?t:TypeDefinition, ?c:Array<Case>, ?h:Bool = false):TypeDefinition {
		if (t == null) {
			t = {
				name: '${cls.name}_$n',
				pack: cls.pack,
				pos: cls.pos,
				meta: [],
				params: [],
				isExtern: false,
				kind: TDClass(),
				fields: [],
			}
		}
		
		switch (e) {
			case { expr: EBlock(exprs), pos: pos }:
				var cases:Array<Case> = [];
				var copy = exprs.copy();
				var sacrifice = exprs.copy();
				var plen = cases.length;
				
				for (expr in copy) {
					
					plen = cases.length;
					loop( expr, n, t, cases, h );
					
					if (cases.length > plen) {
						cases[plen] = transformCase( cases[plen], sacrifice.splice(0, Lambda.indexOf(sacrifice, expr) ) );
					}
					
				}
				
				if (cases.length > 0) {
					
					t.fields.get( 'move' ).body( { expr: EBlock( [ { expr: ESwitch( macro state, cases, null ), pos: e.pos } ] ), pos: e.pos } );
					
					switch (cases[cases.length - 1].expr) {
						case { expr: EBlock(es), pos: pos } :
							es.pop();
							es.push( macro state = -1 );
							
						case _:
							
					}
					
				}
				
			case macro @:yield return $expr:
				setupDef( t );
				
				var _exprs = [];
				_exprs.push( macro state = -1 );
				_exprs.push( macro current = $expr );
				
				
				var _case = {
					values: [macro 0],
					guard: null,
					expr: { expr: EBlock( _exprs ), pos: e.pos }
				};
				
				var index = c.push( _case );
				
				_case.values = [macro $v { index - 1 } ];
				_exprs.push( macro state = $v{ index } );
				
				h = true;
				
			case macro @:yield break:
				setupDef( t );
				h = true;
				
			case macro var $ident:$type = $expr:
				t.fields.push( {
					name: ident.toString(),
					access: [APublic],
					kind: FVar( type ),
					pos: e.pos,
				} );
				
			case _:
				e.iter( function(ee) t = loop(ee, n, t, c, h) );
				
		}
		
		return t;
	}
	
	public static function setupDef(t:TypeDefinition) {
		for (method in ['new', 'hasNext', 'next', 'move']) if (!t.fields.exists( method )) {
			t.fields.push( method.mkField().mkPublic().toFFun().body( macro { } ) );
		}
		
		if (!t.fields.exists( 'state' )) t.fields.push( 'state'.mkField().mkPublic().toFVar( macro :Int ) );
		if (!t.fields.exists( 'current' )) t.fields.push( 'current'.mkField().mkPublic().toFVar( macro :Dynamic ) );
		if (!t.fields.exists( 'iterator' )) t.fields.push( 'iterator'.mkField().mkPublic().toFFun().body( macro return this ) );
		
	}
	
	public static function transformCase(c:Case, chunks:Array<Expr>):Case {
		switch (c.expr.expr) {
			case EBlock(exprs):
				chunks.shift();
				
				// I have to loop through looking for var's and hope it has already been lifted.
				for (chunk in chunks) switch (chunk) {
					case macro var $ident:$type = $expr:
						var _tmp = macro $i { ident } = $expr;
						chunk.expr = _tmp.expr;
						
					case _:
				}
				
				c.expr.expr = EBlock( [ exprs.shift() ].concat( chunks ).concat( exprs ) );
				
			case _:
		}
		
		return c;
	}
	
	public static function finalize(t:TypeDefinition, f:Function) {
		var result = false;
		
		if (t.fields.exists( 'move' )) switch (t.fields.get( 'move' ).kind) {
			case FFun(m): 
				switch (m.expr.expr) {
					case EBlock(exprs) if (exprs.length > 0):
						t.fields.get( 'new' ).body( macro { state = 0; } );
						var copy = exprs.copy();
						t.fields.get( 'next' ).ret( f.ret );
						
						copy.push( macro return current );
						m.expr.expr = EBlock( copy );
						t.fields.get( 'next' ).body( macro { return move(); } );
						t.fields.get( 'hasNext' ).body( macro return state != -1 ).ret( macro:Bool );
						
						Context.defineType( t );
						
						f.expr = Context.parse( 'return new ${t.path()}()', f.expr.pos );
						
						trace( t.printTypeDefinition() );
						trace( f );
					case _:
						
						
				}
				
			case _:
				
				
		}
		
		return result;
	}
	
}