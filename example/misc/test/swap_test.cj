@Test
class SwapTests {
    @TestCase
    func swapExchangesTwoCells(): Unit {
        let l1 = unsafe { CPointer<Int64>(calloc(UIntNative(1), UIntNative(8))) }
        let l2 = unsafe { CPointer<Int64>(calloc(UIntNative(1), UIntNative(8))) }
        unsafe { l1.write(1) }
        unsafe { l2.write(2) }
        swap(l1, l2)
        let a = unsafe { l1.read() }
        let b = unsafe { l2.read() }
        @Expect(a, 2)
        @Expect(b, 1)
        unsafe { free(CPointer<Unit>(l1)) }
        unsafe { free(CPointer<Unit>(l2)) }
    }
}
