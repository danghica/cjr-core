import std.time.*

// One batch produces a checked checksum. Compilation and printing are not timed.
func checked(actual: Int64, expected: Int64): Unit {
    if (actual != expected) {
        throw Exception("checksum mismatch: ${actual}, expected ${expected}")
    }
}

func calibrate(work: () -> Int64, limit: Int64): Int64 {
    var reps: Int64 = 1
    while (true) {
        let start = MonoTime.now()
        var i: Int64 = 0
        var sum: Int64 = 0
        while (i < reps) { sum += work(); i += 1 }
        let elapsed = (MonoTime.now() - start).toNanoseconds()
        // Print calibration checksums too, to keep all work observable.
        println("CAL,${reps},${sum}")
        if (elapsed >= 20000000 || reps >= limit) { return reps }
        reps *= 2
    }
    return reps
}

func sample(name: String, impl: String, n: Int64, ops: Int64, trial: Int64,
            reps: Int64, expected: Int64, work: () -> Int64): Unit {
    let start = MonoTime.now()
    var sum: Int64 = 0
    var i: Int64 = 0
    while (i < reps) { sum += work(); i += 1 }
    let ns = (MonoTime.now() - start).toNanoseconds()
    checked(sum, expected * reps)
    println("BENCH,${name},${impl},${n},${trial},${ns},${ops * reps},${sum}")
}

func benchPair(name: String, n: Int64, ops: Int64, limit: Int64,
               expected: Int64, cj: () -> Int64, std: () -> Int64): Unit {
    checked(cj(), expected)
    checked(std(), expected)
    // Warm both implementations before calibrating them independently.
    checked(cj(), expected); checked(std(), expected)
    let cr = calibrate(cj, limit)
    let sr = calibrate(std, limit)
    var t: Int64 = 0
    while (t < 7) {
        if (t % 2 == 0) {
            sample(name, "CJR", n, ops, t, cr, expected, cj)
            sample(name, "Std", n, ops, t, sr, expected, std)
        } else {
            sample(name, "Std", n, ops, t, sr, expected, std)
            sample(name, "CJR", n, ops, t, cr, expected, cj)
        }
        t += 1
    }
}
