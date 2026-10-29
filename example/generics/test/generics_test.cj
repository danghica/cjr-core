class GenericCounter {
    public var count: Int64 = 0
    public init() {}
}

@Test
class GenericsTests {
    @TestCase
    func identityTypes(): Unit {
        @Expect(genericId<Int64>(42), 42)
        @Expect(genericId<Bool>(true), true)
        @Expect(genericIdAgain<Int64>(-17), -17)
        @Expect(genericIdAgain<Bool>(false), false)
    }

    @TestCase
    func heterogeneousPair(): Unit {
        let p = makePair<Int64, Bool>(7, true)
        @Expect(firstOf<Int64, Bool>(p), 7)
        @Expect(secondOf<Int64, Bool>(p), true)
        let q = Pair<Bool, Int64>(false, -3)
        @Expect(firstOf<Bool, Int64>(q), false)
        @Expect(secondOf<Bool, Int64>(q), -3)
    }

    @TestCase
    func boxRead(): Unit {
        @Expect(makeBox<Int64>(23).get(), 23)
        @Expect(Box<Bool>(false).get(), false)
    }

    @TestCase
    func mapChangesType(): Unit {
        let b = Box<Int64>(5)
        let c = b.map<Bool>({ x: Int64 => x > 0 })
        @Expect(c.get(), true)
        @Expect(b.get(), 5)
        @Expect(Box<Int64>(-1).map<Bool>({ x: Int64 => x > 0 }).get(), false)
    }

    @TestCase
    func extractedLambdaAndLet(): Unit {
        @Expect(positiveBox(3), true)
        @Expect(positiveBox(0), true)
        @Expect(positiveBox(-1), false)
    }

    @TestCase
    func mapComposition(): Unit {
        let b = Box<Int64>(4)
        let c = b.map<Int64>({ x: Int64 => x + 3 }).map<Int64>({ x: Int64 => x * 2 })
        @Expect(c.get(), 14)
        @Expect(b.get(), 4)
    }

    @TestCase
    func nestedInstances(): Unit {
        let p = Pair<Int64, Bool>(8, true)
        let b = genericId<Box<Pair<Int64, Bool>>>(Box<Pair<Int64, Bool>>(p))
        @Expect(firstOf<Int64, Bool>(b.get()), 8)
        @Expect(secondOf<Int64, Bool>(b.get()), true)
        let c = b.map<Box<Bool>>({ x: Pair<Int64, Bool> => Box<Bool>(x.second) })
        @Expect(c.get().get(), true)
    }

    @TestCase
    func sameShapeDifferentNames(): Unit {
        let p = OtherPair<Bool, Int64>(true, 11)
        let q = Pair<Bool, Int64>(false, 19)
        @Expect(p.left, true)
        @Expect(p.right, 11)
        @Expect(q.first, false)
        @Expect(q.second, 19)
        @Expect(OtherBox<Int64>(17).item, 17)
        @Expect(Box<Int64>(18).get(), 18)
    }

    @TestCase
    func eagerBooleanOperands(): Unit {
        let counter = GenericCounter()
        let result = strictAnd({ u: Unit =>
            counter.count += 1
            true
        })
        @Expect(result, false)
        @Expect(counter.count, 1)
    }

    @TestCase
    func recursiveGenericFunction(): Unit {
        @Expect(repeatIdentity<Int64>(71, 0), 71)
        @Expect(repeatIdentity<Bool>(false, 5), false)
        @Expect(repeatIdentity<Pair<Int64, Bool>>(Pair<Int64, Bool>(3, true), 7).first, 3)
    }
}
