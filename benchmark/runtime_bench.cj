func manualSwap(p: CPointer<Int64>, q: CPointer<Int64>): Unit {
    let x=unsafe {p.read()}; unsafe {p.write(q.read());q.write(x)}
}
func corePair(name: String,n: Int64,expected: Int64,cj: () -> Int64,native: () -> Int64): Unit {
    checked(cj(),expected);checked(native(),expected)
    let cr=calibrate(cj,1048576);let nr=calibrate(native,1048576)
    for(t in 0..7) {
        if(t%2==0){sample(name,"CJR",n,n,t,cr,expected,cj);sample(name,"Handwritten",n,n,t,nr,expected,native)}
        else {sample(name,"Handwritten",n,n,t,nr,expected,native);sample(name,"CJR",n,n,t,cr,expected,cj)}
    }
}
@Test
class CoreBenchmarks {
    @TestCase func representative(): Unit {
        let n: Int64=4096
        let p=unsafe {CPointer<Int64>(calloc(UIntNative(1),UIntNative(8)))}
        let q=unsafe {CPointer<Int64>(calloc(UIntNative(1),UIntNative(8)))}
        unsafe {p.write(7);q.write(11)}
        corePair("arithmetic",n,n*(n-1),{=> var s:Int64=0;for(i in 0..n){s+=multiply(i,2)};s},
            {=> var s:Int64=0;for(i in 0..n){s+=i*2};s})
        corePair("swap",n,7,{=>for(_ in 0..n){swap(p,q)};unsafe{p.read()}},
            {=>for(_ in 0..n){manualSwap(p,q)};unsafe{p.read()}})
        corePair("block_sum",n,n*7,{=>var s:Int64=0;for(_ in 0..n){s+=sumAt(p)};s},
            {=>var s:Int64=0;for(_ in 0..n){s+=unsafe{p.read()}};s})
        let b=Box<Int64>(7)
        corePair("generic_callback",n,n*8,{=>var s:Int64=0;for(_ in 0..n){s+=b.map<Int64>({x=>x+1}).get()};s},
            {=>var s:Int64=0;for(_ in 0..n){s+=({x:Int64=>x+1})(b.value)};s})
        unsafe {free(CPointer<Unit>(p));free(CPointer<Unit>(q))}
    }
}
