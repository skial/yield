package uhx.macro;

import uhx.macro.klas.Handler;

/**
 * ...
 * @author Skial Bainn
 */
class Yield {

	public static function initialize() {
		try {
			if (!Handler.setup) {
				Handler.initalize();
			}
			
			Handler.DEFAULTS.push(Wait.handler);
		} catch (e:Dynamic) {
			// This assumes that `implements Klas` is not being used
			// but `@:autoBuild` or `@:build` metadata is being used 
			// with the provided `uhx.macro.Wait.build()` method.
		}
	}
	
}