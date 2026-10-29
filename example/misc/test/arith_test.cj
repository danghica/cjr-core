@Test
class ArithTests {
    @TestCase
    func signedMultiplication(): Unit {
        @Expect(multiply(-7, 6), -42)
        @Expect(multiply(-7, -6), 42)
        @Expect(multiply(0, 9223372036854775807), 0)
        @Expect(multiply(2147483646, 1000000007), 2147483661032385522)
        @Expect(multiply(-2147483646, 1000000007), -2147483661032385522)
    }

    @TestCase
    func signedDivision(): Unit {
        @Expect(divide(7, 3), 2)
        @Expect(divide(-7, 3), -2)
        @Expect(divide(7, -3), -2)
        @Expect(divide(-7, -3), 2)
        @Expect(divide(0, 1), 0)
        @Expect(divide(9223372036854775807, 30), 307445734561825860)
    }

    @TestCase
    func sumOneReturnsOne(): Unit {
        @Expect(sumOne(), 1)
    }
}
