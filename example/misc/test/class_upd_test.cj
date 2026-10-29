@Test
class ClassUpdTests {
    @TestCase
    func classBumpReturnsTheRawWord(): Unit {
        @Expect(classBump(), 0)
    }
}
