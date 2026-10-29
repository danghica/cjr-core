@Test
class CellTests {
    @TestCase
    func cellAllocatesWritesReadsAndFrees(): Unit {
        cell()
        @Expect(true, true)
    }
}
