package uhx.macro;

import haxe.macro.Type;
import haxe.macro.Expr;
import uhx.macro.KlasImp;
import haxe.macro.Context;
import haxe.macro.Printer;

using Lambda;
using StringTools;
using uhx.macro.Yield;
using haxe.macro.TypeTools;
using haxe.macro.ExprTools;
using haxe.macro.MacroStringTools;

/**
 * ...
 * @author Skial Bainn
 */
class Yield {
	
	private static function initialize() {
		try {
			KlasImp.initialize();
			KlasImp.fieldMetadata.add( ':generator', Yield.handler );
		} catch (e:Dynamic) {
			// This assumes that `implements Klas` is not being used
			// but `@:autoBuild` or `@:build` metadata is being used 
			// with the provided `uhx.macro.Yield.build()` method.
		}
	}
	
	public static function build():Array<Field> {
		var cls = Context.getLocalClass().get();
		var fields = Context.getBuildFields();
		for (field in fields.filter( function(f) return f.meta.exists( function(m) return m.name == ':generator') )) {
			field = handler( cls, field );
		}
		return fields;
	}
	
	public static function handler(cls:ClassType, field:Field):Field {
		
		if (field.name == 'new') {
			Context.warning( 'Constructors can not be generators.', field.pos );
			return field;
			
		}
		
		switch (field.kind) {
			case FFun(method):
				if (!Context.defined( 'display' )) {
					
					indent = state = 0;
					ctorBody = [];
					var generator = Context.getLocalType().createGenerator( field.name, method.ret );
					method.expr.startLoop( Context.getBuildFields(), generator );
					generator.finalize( Context.getLocalType(), method );
					
				} else {
					
					var block = switch (method.expr) {
						case { expr:EBlock(_), pos:_ }: method.expr;
						case _: macro { $ { method.expr } };
					}
					
					method.expr = macro { return {
						hasNext:function():Bool return true,
						next:function() untyped $block,
					} };
					
				}
				
				
			case _:
		} 
		
		return field;
	}
	
	public static var state:Int = 0;
	public static var indent:Int = 0;
	public static var block:Expr = null;
	public static var cases:Array<Expr> = null;
	public static var ctorBody:Array<Expr> = null;
	
	public static function createGenerator(cls:Type, methodName:String, returnType:Null<ComplexType>):TypeDefinition {
		if (returnType == null) returnType = macro:Dynamic;
		var _cls = cls.getClass();
		var name = _cls.pack.toDotPath( _cls.name );
		if (name != _cls.module) name = _cls.module + '.' + _cls.name;
		
		var ocls = cls.toComplexType();
		var td = macro class TEMP {
			public var ocls:$ocls;
			public var current:$returnType;
			
			public function new() {	}
			public function hasNext():Bool { }
			public function next():$returnType { }
			public function iterator():Iterator<$returnType> return this;
		}
		td.name = _cls.name + '_' + methodName;
		td.pack = _cls.pack;
		return td;
	}
	
	public static function startLoop(e:Expr, fields:Array<Field>, g:TypeDefinition) {
		switch (e) {
			case { expr: EBlock(es), pos: pos } :
				var copy = es.copy();
				var cases = transformEBlock( copy, fields, g );
				
				if (cases.length > 0) {
					
					for (c in cases) loop( c.expr, fields, g );
					
					g.fields.get( 'next' ).body( { 
						expr: EBlock( [ { 
							expr: ESwitch( macro $i { stateName() }, cases, null ), 
							pos: e.pos 
						} ] ),
						pos: pos
					} );
					
				} else {
					var hasYield = false;
					copy.iter( function (ee) if (loop( ee, fields, g )) hasYield = true );
					
					if (hasYield) {
						for (c in copy) {
							switch (c) {
								case macro var $ident:$type = $expr if (checkIdent( ident.toString(), g ) ):
									copy.remove( c );
									
								case _:
									
							}
						}
						
						switch (g.fields.get( 'next' ).kind) {
							case FFun(m): m.expr.expr = EBlock( copy );
							case _:
						}
					}
				}
				
			case _:
				startLoop( e = { expr: EBlock( [ e ] ), pos: e.pos }, fields, g );
		}
	}
	
	public static function loop(e:Expr, fields:Array<Field>, g:TypeDefinition):Bool {
		var hasYield = false;
		
		switch (e) {
			case { expr: EBlock(es), pos: pos } :
				var copy = es.copy();
				var cases = transformEBlock( copy, fields, g );
				
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
					
					for (c in cases) loop( c.expr, fields, g );
					
				} else {
					copy.iter( function(ee) if (loop(ee, fields, g)) hasYield = true );
					if (hasYield) e.expr = EBlock( copy );
				}
				
			case macro for ($ident in $expr) $block:
				liftIdent( ident.toString(), g, ident.try_ctype(), expr );
				
				if (loop( block, fields, g )) {
					
					switch (expr) {
						case macro $start...$end:
							g.fields.get( ident.toString() ).kind == FVar( macro:Int );
							e.expr = ( macro {
								if ($ident == null) $ident = $start;
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
				if (loop( block, fields, g )) {
					
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
				
				if (loop( ifblock, fields, g )) {
					hasYield = true;
					cond.expr = (macro $e { Reflect.copy(cond) } && $i { stateName() } > -1).expr;
					ifblock.expr = (macro { $e { Reflect.copy(ifblock) }; return current; } ).expr;
				}
				
				if (elseblock != null && loop( elseblock, fields, g )) {
					hasYield = true;
				}
				
			case _:
				e.iter( function(ee) if (loop( ee, fields, g )) hasYield = true );
				
		}
		
		return hasYield;
	}
	
	public static function finalize(td:TypeDefinition, cls:Type, f:Function) {
		var next = td.fields.get( 'next' );
		
		if (next != null) switch (next.kind) {
			case FFun(m): 
				switch (m.expr.expr) {
					case EBlock(exprs) if (exprs.length > 0):
						var returnType = cls.toComplexType();
						if (returnType == null) returnType = f.ret != null ? f.ret : macro:Dynamic;
						var ctor = td.fields.get( 'new' );
						var ctor_args = ctor.args();
						
						for (i in 0...state) { 
							td.fields.push( { name: 'state$i', access: [APublic], kind: FVar( macro :Int ), pos: exprs[0].pos } );
							ctorBody.push( macro $i { 'state$i' } = 0 );
						};
						
						var arg_names = [];
						
						for (arg in f.args) {
							ctor_args.push( arg );
							arg_names.push( arg.name );
							td.fields.push( { name: arg.name, access: [APublic], kind: FVar( arg.type ), pos: f.expr.pos } );
							ctorBody.push( Context.parse('this.${arg.name} = ${arg.name}', f.expr.pos) );
						}
						
						// Add a reference to the calling class as an arg
						arg_names.push( 'this' );
						ctorBody.push( Context.parse('this.ocls = ocls', f.expr.pos) );
						ctor_args.push( { name: 'ocls', opt: false, type: cls.toComplexType() } );
						
						var copy = exprs.copy();
						function liftUnknownAccess(e:Expr) {
							switch (e) {
								case { expr: EConst(CIdent( id )), pos: pos } if (['null', 'true', 'false'].indexOf(id) == -1 && td.fields.get( id ) == null):
									td.fields.push( { name: id, kind: FProp('get', 'set', macro:Dynamic, null), pos:e.pos } );
									td.fields.push( { name: 'get_$id', kind: FFun({
										args:[], 
										expr: (macro { return $p { ['ocls', id] } }), 
										ret:null,
									}), pos: e.pos } );
									td.fields.push( { name: 'set_$id', kind: FFun({
										args:[ { name:'v', type:macro:Dynamic } ], 
										expr: (macro { return $p { ['ocls', id] } = $i{'v'} } ),
										ret:null,
									}), pos: e.pos } );
									
								case _:
									e.iter( liftUnknownAccess );
									
							}
						}
						copy.iter( liftUnknownAccess );
						
						ctor.body( { expr: EBlock( ctorBody ), pos: ctorBody[0].pos } );
						
						copy.push( macro return current );
						m.expr.expr = EBlock( copy );
						var checks = [for (i in 0...state) macro $i { 'state$i' } > -1];
						var statement = checks.pop();
						for (check in checks) statement = macro $statement || $check;
						
						td.fields.get( 'hasNext' ).body( macro return $statement );
						
						f.expr = { expr:EBlock( [Context.parse( 'return new ${td.pack.toDotPath(td.name)}(${arg_names.join(",")})', f.expr.pos )] ), pos:f.expr.pos };
						if (f.ret != null) f.ret = TPath( { name:'Iterator', pack:[], params: [TPType(returnType)] } );
						//trace( new Printer().printTypeDefinition( td ) );
						//trace( new Printer().printFunction( f ) );
						Context.defineType( td );
						
					case _:
						
						
				}
				
			case _:
				
				
		}
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
		if (!g.fields.match( ident )) {
			
			g.fields.push( {
				name: ident,
				access: [APublic],
				kind: FVar( ctype ),
				pos: expr.pos,
			} );
			
		}
	}
	
	public static function checkIdent(ident:String, g:TypeDefinition) {
		return g.fields.match( ident );
	}
	
	public static function transformEBlock(exprs:Array<Expr>, fields:Array<Field>, g:TypeDefinition):Array<Case> {
		var cls = Context.getLocalClass().get();
		var result = [];
		var _prev = [];
		var _exprs = [];
		var _case = null;
		var _index = 0;
		
		for (e in exprs) {
			
			_case = { values: [macro 0], guard: null, expr: null };
			
			switch (e) {
				case macro $ident($a { args } ) if (fields.match( ident.toString() )):
					var field = fields.get( ident.toString() );
					var call = field.access.indexOf( AStatic ) == -1 ? 'ocls' : cls.pack.toDotPath( cls.name );
					var ee = Context.parse('$call.${ident.toString()}', e.pos);
					//e.expr = ().expr;
					_prev.push( macro $ee($a { args } ) );
					
				case macro var $ident:$type = $expr:
					liftIdent( ident.toString(), g, type == null ? expr.try_ctype() : type, expr );
					ctorBody.push( macro $i { ident.toString() } = $expr );
					
				case macro return $e:
					_exprs = [macro $i { 'state$state' } = -1, macro current = $e].concat( _prev );
					_prev = [];
					_case.expr = { expr: EBlock( _exprs ), pos: e.pos };
					
					_index = result.push( _case );
					_exprs.push( macro $i { 'state$state' } = $v { _index } );
					
					_case.values = [macro $v { _index - 1 } ];
					
				case macro break:
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
	
	public static function get(fields:Array<Field>, ident:String):Field return fields.filter( function(f) return f.name == ident )[0];
	public static function match(fields:Array<Field>, ident:String) return fields.exists( function(f) return f.name == ident );
	public static function method(field:Field) return switch (field.kind) {
		case FFun(m): m;
		case _: null;
	}
	public static function args(field:Field) return method( field ).args;
	public static function body(field:Field, nbody:Expr) method( field ).expr = nbody;
	public static function ret(field:Field, nret:ComplexType) method( field ).ret = nret;
	public static inline function try_ctype(expr:Expr) return try Context.typeof( expr ).toComplexType() catch (e:Dynamic) macro:Dynamic;
	
}