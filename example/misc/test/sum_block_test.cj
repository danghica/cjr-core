@Test
class SumBlockTests {
    @TestCase
    func sumAtReadsTheWrittenWord(): Unit {
        let p = unsafe { CPointer<Int64>(calloc(UIntNative(1), UIntNative(8))) }
        unsafe { p.write(4) }
        let s = sumAt(p)
        @Expect(s, 4)
        unsafe { free(CPointer<Unit>(p)) }
    }
}
