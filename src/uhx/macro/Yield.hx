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
			case FFun(method) if(method.expr != null): loop( method.expr, field );
			case _:
		}
		
		return fields;
	}
	
	public static var name:String = null;
	
	public static function loop(e:Expr, f:Field, ?t:TypeDefinition):TypeDefinition {
		if (t == null) {
			t = {
				name: '${cls.name}_${f.name}',
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
			case { expr: EBlock(block), pos: pos }:
				trace( block.length );
				
			case macro @:yield return $expr:
				trace( expr );
				
			case macro @:yield break:
				
				
			case macro var $ident:$type:
				t.fields.push( {
					name: ident.toString(),
					access: [APublic],
					kind: FVar( type ),
					pos: f.pos,
				} );
				
			case _:
				e.iter( function(ee) t = loop(ee, f, t) );
				
		}
		
		return t;
	}
	
}