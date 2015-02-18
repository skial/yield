Yield
=====

An experiment to recreate CSharp's yield syntax sugar which
converts methods into iterators for lazy enumeration.

## Install

`haxelib git yield https://github.com/skial/yield.git`
	
And add `-lib yield` to your `hxml` file.
	
## Usage

You have two options, use Yield with [Klas](https://github.com/skial/klas/) or not.

#### With Klas

```
package ;

class Main implements Klas {
	
	public function new() {
		for (i in test()) {
			trace( i );
			// 1
			// 10
			// 100
			// 1000
		}
	}
	
	@:generator public function test() {
		return 1;
		return 10;
		return 100;
		return 1000;
	}
	
}
```

#### Without Klas


```
package ;

@:autoBuild( uhx.macro.Yield.build() )
class Main {
	
	public function new() {
		for (i in test()) {
			trace( i );
			// 1
			// 10
			// 100
			// 1000
		}
	}
	
	@:generator public function test() {
		return 1;
		return 10;
		return 100;
		return 1000;
	}
	
}
```

## Explanation

Yield converts your methods marked with `@:generator` into 
separate classes. The method in both examples above called
`test` gets transformed into the following class.

```
class Main_test {
        public var ocls : Main;
        public var current : Dynamic;
        public function new(ocls:Main) {
                state0 = 0;
                this.ocls = ocls;
        }
        public function hasNext():Bool return state0 > -1;
        public function next() {
                switch state0 {
                        case 0:{
                                state0 = -1;
                                current = 1;
                                state0 = 1;
                        };
                        case 1:{
                                state0 = -1;
                                current = 10;
                                state0 = 2;
                        };
                        case 2:{
                                state0 = -1;
                                current = 100;
                                state0 = 3;
                        };
                        case 3:{
                                state0 = -1;
                                current = 1000;
                                state0 = -2;
                        };
                };
                return current;
        }
        public function iterator() return this;
        public var state0 : Int;
}
```

## Tests

You can find Yields tests in the [uhu-spec](https://github.com/skial/uhu-spec/blob/master/src/uhx/macro/YieldSpec.hx) library.