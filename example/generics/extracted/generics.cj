// Generated from checked CJR generic source; do not edit.
import std.core.Array as CjrBuffer
public struct Pair<A, B> {
public let first: A
public let second: B
public init(first: A, second: B) {
this.first = first
this.second = second
}
}
public class Box<T> {
public let value: T
public init(value: T) {
this.value = value
}
public func get(): T {
let self = this
return (({ cjrTypedValue: Box<T> => cjrTypedValue })(self)).value
}
public func map<U>(f: (T) -> U): Box<U> {
let self = this
return Box<U>((f)((({ cjrTypedValue: Box<T> => cjrTypedValue })(self)).value))
}
}
public struct OtherPair<A, B> {
public let left: A
public let right: B
public init(left: A, right: B) {
this.left = left
this.right = right
}
}
public class OtherBox<T> {
public let item: T
public init(item: T) {
this.item = item
}
}
public func genericId<T>(x: T): T {
return x
}
public func genericIdAgain<T>(x: T): T {
return x
}
public func firstOf<A, B>(p: Pair<A, B>): A {
return (({ cjrTypedValue: Pair<A, B> => cjrTypedValue })(p)).first
}
public func secondOf<A, B>(p: Pair<A, B>): B {
return (({ cjrTypedValue: Pair<A, B> => cjrTypedValue })(p)).second
}
public func repeatIdentity<T>(x: T, n: Int64): T {
return if ((n  <=  0)) { x } else { repeatIdentity<T>(x, (n  -  1)) }
}
public func makePair<A, B>(a: A, b: B): Pair<A, B> {
return Pair<A, B>(a, b)
}
public func makeBox<T>(x: T): Box<T> {
return Box<T>(x)
}
public func positiveBox(n: Int64): Bool {
return ({ => 
let b = Box<Int64>(n)
(({ cjrTypedValue: Box<Bool> => cjrTypedValue })((({ cjrTypedValue: Box<Int64> => cjrTypedValue })(b)).map<Bool>({ x: Int64 => ({ cjrTypedValue: Bool => cjrTypedValue })((0  <=  x)) }))).get()
})()
}
public func strictAnd(f: (Unit) -> Bool): Bool {
return ({ cjrLeft: Bool, cjrRight: Bool => cjrLeft && cjrRight })(false, (f)(()))
}
main() {
genericId<Int64>(42)
0
}
