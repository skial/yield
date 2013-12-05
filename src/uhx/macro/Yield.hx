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
	
	public static function handler(cls:ClassType, fields:Array<Field>):Array<Field> {
		Yield.cls = cls;
		
		if (!Context.defined( 'display' )) for (field in fields) switch (field.kind) {
			case FFun(method) if (method.expr != null):
				indent = state = 0;
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
					
					generator.fields.get( 'move' ).getMethod().expr.expr = EBlock( [ { 
						expr: ESwitch( macro $i { 'state' + (state-1) }, cases, null ), 
						pos: e.pos 
					} ] );
					
				} else {
					var hasYield = false;
					copy.iter( function (ee) if (loop(ee, n)) hasYield = true );
					if (hasYield) generator.fields.get( 'move' ).getMethod().expr.expr = EBlock( copy );
				}
				
			case _:
				entry( e = { expr: EBlock( [ e ] ), pos: e.pos }, n );
		}
	}
	
	public static function loop(e:Expr, n:String, ?r:Expr = null):Bool {
		var hasYield = false;
		
		switch (e) {
			case { expr: EBlock(es), pos: pos } :
				var copy = es.copy();
				var cases = transformEBlock( copy );
				
				if (cases.length > 0) {
					
					hasYield = true;
					
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
					e.expr = (macro $i { 'block$indent' } ()).expr;
					
					indent++;
					
				} else {
					copy.iter( function(ee) if (loop(ee, n)) hasYield = true );
					if (hasYield) e.expr = EBlock( copy );
				}
				
			case macro var $ident:$type = $expr:
				var ctype = type;
				
				if (ctype == null) try {
					ctype = Context.typeof( expr ).toCType();
				} catch (e:Dynamic) { 
					// Who care's.
				}
				
				generator.fields.push( {
					name: ident.toString(),
					access: [APublic],
					kind: FVar( ctype ),
					pos: e.pos,
				} );
				
			case macro for ($ident in $expr) $block:
				generator.fields.push( {
					name: ident.toString(),
					access: [APublic],
					kind: FVar( null ),
					pos: e.pos,
				} );
				
				if (loop( block, n )) {
					
					switch (expr) {
						case macro $start...$end:
							generator.fields.get( ident.toString() ).toFVar( Context.typeof( start ).toCType() );
							e.expr = ( macro {
								if ($ident == null ) $ident = $start;
								while ($ident < $end) {
									$block;
									if ($i { 'state' + (state-1) } == 0 ) $ident++;
									if ($ident == $end ) $i { 'state' + (state-1) } = -1;
									break;
								}
							} ).expr;
							
						case _:
							
					}
					
					hasYield = true;
					/*var field = generator.fields[generator.fields.length -1];
					
					switch (field.getMethod().expr) {
						case { expr: EBlock(es), pos: pos } :
							for (e in es) switch (e) {
								case { expr: ESwitch(ident, cases, _), pos: pos } :
									switch (cases[cases.length - 1].expr) {
										case { expr: EBlock(es), pos: pos } :
											es.pop();
											es.push( macro $ident = 0 );
											
										case _:
											
									}
									
								case _:
									
							}
							
						case _:
							
					}*/
					loopBlock( generator.fields[generator.fields.length -1] );
					
				}
				
			case macro while ($cond) $block:
				
				if (loop( block, n )) {
					
					e.expr = (macro if ($cond) $block).expr;
					
					hasYield = true;
					loopBlock( generator.fields[generator.fields.length -1] );
					
				}
				
			case macro @:yield break:
				e.expr = ( macro $i { 'state' + (state-1) } = -1 ).expr;
				
			case _:
				e.iter( function(ee) if (loop(ee, n)) hasYield = true );
				
		}
		
		return hasYield;
	}
	
	public static function loopBlock(field:Field) {
		switch (field.getMethod().expr) {
			case { expr: EBlock(es), pos: pos } :
				for (e in es) switch (e) {
					case { expr: ESwitch(ident, cases, _), pos: pos } :
						switch (cases[cases.length - 1].expr) {
							case { expr: EBlock(es), pos: pos } :
								es.pop();
								es.push( macro $ident = 0 );
								
							case _:
								
						}
						
					case _:
						
				}
				
			case _:
				
		}
	}
	
	public static function finalizeYieldClass(t:TypeDefinition, f:Function) {
		var result = false;
		
		if (t.fields.exists( 'move' )) switch (t.fields.get( 'move' ).kind) {
			case FFun(m): 
				switch (m.expr.expr) {
					case EBlock(exprs) if (exprs.length > 0):
						var es = [for (i in 0...state) { 
							t.fields.push( { name: 'state$i', access: [APublic], kind: FVar( macro :Int ), pos: exprs[0].pos } );
							macro $i { 'state$i' } = 0;
						} ];
						
						
						var anames = [];
						for (arg in f.args) {
							t.fields.get( 'new' ).args().push( arg );
							t.fields.push( { name: arg.name, access: [APublic], kind: FVar( arg.type ), pos: f.expr.pos } );
							es.push( Context.parse('this.${arg.name} = ${arg.name}', f.expr.pos) );
							anames.push( arg.name );
						}
						
						t.fields.get( 'new' ).body( { expr: EBlock( es ), pos: es[0].pos } );
						
						var copy = exprs.copy();
						t.fields.get( 'next' ).ret( f.ret );
						
						copy.push( macro return current );
						m.expr.expr = EBlock( copy );
						t.fields.get( 'next' ).body( macro { return move(); } );
						t.fields.get( 'hasNext' ).body( macro return state0 != -1 ).ret( macro:Bool );
						
						Context.defineType( t );
						
						f.expr = Context.parse( 'return new ${t.path()}(${anames.join("\'")})', f.expr.pos );
						
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
					
				case macro @:yield break:
					_prev.push( macro $i { 'state$state' } = -1 );
					
				case _:
					_prev.push( expr );
					
			}
			
		}
		
		if (result.length > 0) {
			state++;
			finalizeCases( result );
		}
		
		return result;
	}
	
}