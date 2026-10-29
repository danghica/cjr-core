@Test
class StructUpdTests {
    @TestCase
    func bumpWritesTheField(): Unit {
        @Expect(bump(), 1)
    }

    @TestCase
    func bumpKeepLeavesTheRawWord(): Unit {
        @Expect(bumpKeep(), 0)
    }
}
