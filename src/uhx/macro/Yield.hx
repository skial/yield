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
	public static var generator:TypeDefinition = null;
	public static var hasYield:Bool = false;
	
	public static function handler(cls:ClassType, fields:Array<Field>):Array<Field> {
		Yield.cls = cls;
		
		if (!Context.defined( 'display' )) for (field in fields) switch (field.kind) {
			case FFun(method) if (method.expr != null):
				hasYield = false;
				setupYieldClass( generator = createYieldClass( field.name ) );
				entry( method.expr, field.name );
				finalizeYieldClass( generator, method );
				
			case _:
		}
		
		return fields;
	}
	
	public static var name:String = null;
	public static var cases:Array<Expr> = null;
	public static var state:Int = 0;
	public static var indent:Int = 0;
	public static var block:Expr = null;
	
	public static function createYieldClass(n:String):TypeDefinition {
		return {
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
	
	public static function setupYieldClass(t:TypeDefinition) {
		for (method in ['new', 'hasNext', 'next', 'move']) if (!t.fields.exists( method )) {
			t.fields.push( method.mkField().mkPublic().toFFun().body( macro { } ) );
		}
		
		//if (!t.fields.exists( 'state' )) t.fields.push( 'state'.mkField().mkPublic().toFVar( macro :Int ) );
		if (!t.fields.exists( 'current' )) t.fields.push( 'current'.mkField().mkPublic().toFVar( macro :Dynamic ) );
		if (!t.fields.exists( 'iterator' )) t.fields.push( 'iterator'.mkField().mkPublic().toFFun().body( macro return this ) );
	}
	
	public static function entry(e:Expr, n:String) {
		switch (e) {
			case { expr: EBlock(es), pos: pos } :
				var copy = es.copy();
				var cases = transformEBlock( copy );
				
				if (cases.length > 0) {
					
					for (c in cases) loop( c.expr, n, c.expr );
					
					block = generator.fields.get( 'move' ).getMethod().expr;
					block.expr = EBlock( [ { expr: ESwitch( macro $i{ 'state' + (state-1) }, cases, null ), pos: e.pos } ] );
					
				} else {
					copy.iter( loop.bind(_, n) );
					if (hasYield) generator.fields.get( 'move' ).getMethod().expr.expr = EBlock( copy );
				}
				
			case _:
				entry( e = { expr: EBlock( [ e ] ), pos: e.pos }, n );
		}
	}
	
	public static function loop(e:Expr, n:String, ?r:Expr = null) {
		
		switch (e) {
			case { expr: EBlock(es), pos: pos } :
				var copy = es.copy();
				var cases = transformEBlock( copy );
				
				if (cases.length > 0) {
					
					var method = {
						name: 'block$indent',
						access: [APublic],
						kind: FFun( {
							args: [],
							ret: null,
							params: [],
							expr: { expr: EBlock( [ { expr: ESwitch( macro $i { 'state' + (state-1) }, cases, null ), pos: e.pos } ] ), pos: e.pos },
						} ),
						pos: e.pos,
					};
					
					generator.fields.push( method );
					e.expr = EBlock( [ macro $i { 'block$indent' }() ] );
					
					indent++;
					
				} else {
					copy.iter( loop.bind(_, n) );
					if (hasYield) e.expr = EBlock( copy );
				}
				
			case macro var $ident:$type = $expr:
				generator.fields.push( {
					name: ident.toString(),
					access: [APublic],
					kind: FVar( type ),
					pos: e.pos,
				} );
				
			/*case macro for ($ident in $expr) $block:
				var exprs = block.expr.getParameters()[0];
				var copy = exprs.copy();
				var cases = transformEBlock( copy );
				
				if (cases.length > 0) {
					block.expr = EBlock( [ { expr: ESwitch( macro state, cases, null ), pos: block.pos } ] );
				} else {
					exprs.iter( loop.bind(_, n) );
				}*/
				
			case _:
				e.iter( loop.bind(_, n) );
				
		}
		
	}
	
	public static function finalizeYieldClass(t:TypeDefinition, f:Function) {
		var result = false;
		trace( t.printTypeDefinition() );
		if (t.fields.exists( 'move' )) switch (t.fields.get( 'move' ).kind) {
			case FFun(m): 
				switch (m.expr.expr) {
					case EBlock(exprs) if (exprs.length > 0):
						var es = [for (i in 0...state) macro $i { 'state$i' } = 0];
						t.fields.get( 'new' ).body( { expr: EBlock( es ), pos: es[0].pos } );
						var copy = exprs.copy();
						t.fields.get( 'next' ).ret( f.ret );
						
						copy.push( macro return current );
						m.expr.expr = EBlock( copy );
						t.fields.get( 'next' ).body( macro { return move(); } );
						t.fields.get( 'hasNext' ).body( macro return state0 != -1 ).ret( macro:Bool );
						
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
	
	public static function finalizeCases(cases:Array<Case>) {
		switch (cases[cases.length - 1].expr) {
			case { expr: EBlock(es), pos: pos } :
				es.pop();
				es.push( macro $i{ 'state' + (state-1) } = -1 );
				
			case _:
				
		}
	}
	
	public static function transformEBlock(exprs:Array<Expr>):Array<Case> {
		var result = [];
		var _prev = [];
		var _exprs = [];
		var _case = null;
		var _index = 0;
		
		for (expr in exprs) {
			
			_case = { values: [macro 0], guard: null, expr: null };
			
			switch (expr) {
				case macro @:yield return $e:
					_exprs = [macro $i { 'state$state' } = -1, macro current = $e].concat( _prev );
					_prev = [];
					_case.expr = { expr: EBlock( _exprs ), pos: e.pos };
					
					_index = result.push( _case );
					_exprs.push( macro $i { 'state$state' } = $v { _index } );
					
					_case.values = [macro $v { _index - 1 } ];
					
					hasYield = true;
					
				case macro @:yield break:
					
					
				case _:
					_prev.push( expr );
					
			}
			
		}
		
		if (result.length > 0) {
			generator.fields.push( { name: 'state$state', access: [APublic], kind: FVar( macro :Int ), pos: exprs[0].pos } );
			state++;
			finalizeCases( result );
		}
		
		return result;
	}
	
}