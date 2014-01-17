package uhx.macro;

import haxe.macro.Type;
import haxe.macro.Expr;
import haxe.macro.Context;
import uhx.macro.KlasImpl;

using uhu.macro.Jumla;
using haxe.macro.ExprTools;
using haxe.macro.MacroStringTools;

/**
 * ...
 * @author Skial Bainn
 */
class Yield {

	private static function initialize() {
		try {
			if (!KlasImpl.setup) {
				KlasImpl.initalize();
			}
			
			KlasImpl.DEFAULTS.set('Yield', Yield.handler);
		} catch (e:Dynamic) {
			// This assumes that `implements Klas` is not being used
			// but `@:autoBuild` or `@:build` metadata is being used 
			// with the provided `uhx.macro.Yield.build()` method.
		}
	}
	
	public static function build():Array<Field> {
		return handler( Context.getLocalClass().get(), Context.getBuildFields() );
	}
	
	public static function handler(cls:ClassType, fields:Array<Field>):Array<Field> {
		
		if (!Context.defined( 'display' )) for (field in fields) switch (field.kind) {
			case FFun(method) if (method.expr != null):
				indent = state = 0;
				newBody = [];
				var generator = createYieldClass( field.name, cls );
				setupYieldClass( cls, generator );
				entry( method.expr, field.name, cls, fields, generator );
				finalizeYieldClass( cls, generator, method );
				
			case _:
		}
		
		return fields;
	}
	
	public static var name:String = null;
	public static var cases:Array<Expr> = null;
	public static var state:Int = 0;
	public static var indent:Int = 0;
	public static var block:Expr = null;
	public static var newBody:Array<Expr> = null;
	
	public static function createYieldClass(n:String, cls:ClassType):TypeDefinition {
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
	
	public static function setupYieldClass(cls:ClassType, t:TypeDefinition) {
		for (method in ['new', 'hasNext', 'next']) if (!t.fields.exists( method )) {
			t.fields.push( method.mkField().mkPublic().toFFun().body( macro { } ) );
		}
		
		if (!t.fields.exists( 'ocls' )) t.fields.push( 'ocls'.mkField().mkPublic().toFVar( Context.getType( cls.path() ).toCType() ) );
		if (!t.fields.exists( 'current' )) t.fields.push( 'current'.mkField().mkPublic().toFVar( macro :Dynamic ) );
		if (!t.fields.exists( 'iterator' )) t.fields.push( 'iterator'.mkField().mkPublic().toFFun().body( macro return this ) );
	}
	
	public static function entry(e:Expr, n:String, cls:ClassType, fields:Array<Field>, g:TypeDefinition) {
		switch (e) {
			case { expr: EBlock(es), pos: pos } :
				var copy = es.copy();
				var cases = transformEBlock( copy, cls, fields, g );
				
				if (cases.length > 0) {
					
					for (c in cases) loop( c.expr, n, cls, fields, g, c.expr );
					
					g.fields.get( 'next' ).getMethod().expr.expr = EBlock( [ { 
						expr: ESwitch( macro $i { stateName() }, cases, null ), 
						pos: e.pos 
					} ] );
					
				} else {
					var hasYield = false;
					copy.iter( function (ee) if (loop( ee, n, cls, fields, g )) hasYield = true );
					
					if (hasYield) {
						for (c in copy) {
							switch (c) {
								case macro var $ident:$type = $expr if (checkIdent( ident.toString(), g ) ):
									copy.remove( c );
									
								case _:
									
							}
						}
						
						g.fields.get( 'next' ).getMethod().expr.expr = EBlock( copy );
					}
				}
				
			case _:
				entry( e = { expr: EBlock( [ e ] ), pos: e.pos }, n, cls, fields, g );
		}
	}
	
	public static function loop(e:Expr, n:String, cls:ClassType, fields:Array<Field>, g:TypeDefinition, ?r:Expr = null):Bool {
		var hasYield = false;
		
		switch (e) {
			case { expr: EBlock(es), pos: pos } :
				var copy = es.copy();
				var cases = transformEBlock( copy, cls, fields, g );
				
				if (cases.length > 0) {
					
					hasYield = true;
					
					var method = {
						name: 'block$indent',
						access: [APublic],
						kind: FFun( {
							args: [],
							ret: null,
							params: [],
							expr: { expr: EBlock( [ { expr: ESwitch( macro $i { stateName() }, cases, null ), pos: e.pos } ] ), pos: e.pos },
						} ),
						pos: e.pos,
					};
					
					g.fields.push( method );
					
					e.expr = (macro $i { 'block$indent' } ()).expr;
					
					indent++;
					
					for (c in cases) loop( c.expr, n, cls, fields, g, c.expr );
					
				} else {
					copy.iter( function(ee) if (loop(ee, n, cls, fields, g)) hasYield = true );
					if (hasYield) e.expr = EBlock( copy );
				}
				
			case macro for ($ident in $expr) $block:
				liftIdent( ident.toString(), g, null, expr );
				
				if (loop( block, n, cls, fields, g )) {
					
					switch (expr) {
						case macro $start...$end:
							g.fields.get( ident.toString() ).toFVar( Context.typeof( start ).toCType() );
							e.expr = ( macro {
								if ($ident == null ) $ident = $start;
								while ($ident < $end) {
									$block;
									if ($i { stateName() } == 0 ) $ident++;
									if ($ident == $end ) $i { stateName() } = -2;
									break;
								}
							} ).expr;
							
						case _:
							
					}
					
					hasYield = true;
					loopBlock( g.fields[g.fields.length -1] );
					
				}
				
			case macro while ($cond) $block:
				if (loop( block, n, cls, fields, g )) {
					
					e.expr = (macro if ($cond) $block).expr;
					
					hasYield = true;
					loopBlock( g.fields[g.fields.length -1] );
					
				}
				
			case { expr: EIf(cond, ifblock, elseblock), pos: pos } :
				
				switch(ifblock) {
					case { expr: EBlock(es), pos: pos } :
					case _: 
						ifblock.expr = (macro { $e { Reflect.copy( ifblock ) } } ).expr;
				}
				
				if (loop( ifblock, n, cls, fields, g )) {
					hasYield = true;
					cond.expr = (macro $e { Reflect.copy(cond) } && $i { stateName() } > -1).expr;
					ifblock.expr = (macro { $e { Reflect.copy(ifblock) }; return current; } ).expr;
				}
				
				if (elseblock != null && loop( elseblock, n, cls, fields, g )) {
					hasYield = true;
				}
				
			case _:
				e.iter( function(ee) if (loop( ee, n, cls, fields, g )) hasYield = true );
				
		}
		
		return hasYield;
	}
	
	public static function finalizeYieldClass(cls:ClassType, t:TypeDefinition, f:Function) {
		var result = false;
		
		if (t.fields.exists( 'next' )) switch (t.fields.get( 'next' ).kind) {
			case FFun(m): 
				switch (m.expr.expr) {
					case EBlock(exprs) if (exprs.length > 0):
						for (i in 0...state) { 
							t.fields.push( { name: 'state$i', access: [APublic], kind: FVar( macro :Int ), pos: exprs[0].pos } );
							newBody.push( macro $i { 'state$i' } = 0 );
						};
						
						var anames = [];
						for (arg in f.args) {
							t.fields.get( 'new' ).args().push( arg );
							t.fields.push( { name: arg.name, access: [APublic], kind: FVar( arg.type ), pos: f.expr.pos } );
							newBody.push( Context.parse('this.${arg.name} = ${arg.name}', f.expr.pos) );
							anames.push( arg.name );
						}
						
						// Add a reference to the calling class as an arg
						anames.push( 'this' );
						newBody.push( Context.parse('this.ocls = ocls', f.expr.pos) );
						t.fields.get( 'new').args().push( { name:'ocls', opt:false, type:Context.getType( cls.path() ).toCType() } );
						
						t.fields.get( 'new' ).body( { expr: EBlock( newBody ), pos: newBody[0].pos } );
						
						var copy = exprs.copy();
						t.fields.get( 'next' ).ret( f.ret );
						
						copy.push( macro return current );
						m.expr.expr = EBlock( copy );
						t.fields.get( 'hasNext' ).body( macro return state0 > -1 ).ret( macro:Bool );
						
						Context.defineType( t );
						f.expr = Context.parse( 'return new ${t.path()}(${anames.join(",")})', f.expr.pos );
						
					case _:
						
						
				}
				
			case _:
				
				
		}
		
		return result;
	}
	
	/**
	 * -1 == Error
	 * -2 == End
	 */
	
	public static function finalizeCases(cases:Array<Case>) {
		switch (cases[cases.length - 1].expr) {
			case { expr: EBlock(es), pos: pos } :
				es.pop();
				es.push( macro $i{ stateName() } = -2 );
				
			case _:
				
		}
	}
	
	public static function loopBlock(field:Field) {
		switch (field.kind) {
			case FFun(m):
				switch (m.expr) {
					case { expr: EBlock(es), pos: pos } :
						for (e in es) switch (e) {
							case { expr: ESwitch(ident, cases, _), pos: pos } :
								switch (cases[cases.length - 1].expr) {
									case { expr: EBlock(es), pos: pos } :
										es.pop();
										es.push( macro if ($ident > -2) $ident = 0 );
										
									case _:
										
								}
								
							case _:
								
						}
						
					case _:
						
				}
				
			case _:
				
		}
		
	}
	
	public static function liftIdent(ident:String, g:TypeDefinition, ?ctype:ComplexType, ?expr:Expr) {
		if (!g.fields.exists( ident )) {
			
			if (ctype == null) try {
				ctype = Context.typeof( expr ).toCType();
			} catch (e:Dynamic) { 
				// Who care's.
			}
			
			g.fields.push( {
				name: ident,
				access: [APublic],
				kind: FVar( ctype ),
				pos: expr.pos,
			} );
			
		}
	}
	
	public static function checkIdent(ident:String, g:TypeDefinition) {
		return g.fields.exists( ident );
	}
	
	public static function transformEBlock(exprs:Array<Expr>, cls:ClassType, fields:Array<Field>, g:TypeDefinition):Array<Case> {
		var result = [];
		var _prev = [];
		var _exprs = [];
		var _case = null;
		var _index = 0;
		
		for (e in exprs) {
			
			_case = { values: [macro 0], guard: null, expr: null };
			
			switch (e) {
				case macro $ident($a { args } ) if (fields.exists( ident.toString() )):
					var field = fields.get( ident.toString() );
					var call = field.access.indexOf( AStatic ) == -1 ? 'ocls' : cls.pack.toDotPath( cls.name );
					var ee = Context.parse('$call.${ident.toString()}', e.pos);
					//e.expr = ().expr;
					_prev.push( macro $ee($a { args } ) );
					
				case macro var $ident:$type = $expr:
					liftIdent( ident.toString(), g, type, expr );
					//var array = result.length == 0 ? newBody : _prev;
					var array = newBody;
					array.push( macro $i { ident.toString() } = $expr );
					
				case macro @:yield return $e:
					_exprs = [macro $i { 'state$state' } = -1, macro current = $e].concat( _prev );
					_prev = [];
					_case.expr = { expr: EBlock( _exprs ), pos: e.pos };
					
					_index = result.push( _case );
					_exprs.push( macro $i { 'state$state' } = $v { _index } );
					
					_case.values = [macro $v { _index - 1 } ];
					
				case macro @:yield break:
					e.expr = (macro { $i { stateName() } = -2; } ).expr;
					
				case _:
					_prev.push( e );
					
			}
			
		}
		
		if (result.length > 0) {
			state++;
			finalizeCases( result );
		}
		
		return result;
	}
	
	public static function stateName():String {
		return 'state' + (state-1 < 0 ? 0 : state-1);
	}
	
}