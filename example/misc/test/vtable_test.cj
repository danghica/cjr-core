@Test
class VTableTests {
    @TestCase
    func runAppliesTheStoredClosure(): Unit {
        @Expect(run(), 1)
    }
}
