package utils;

import java.util.Optional;

/**
 * Medium-quality random numbers using a basic XOR-shift algorithm (for underlying basic algorithm see, e.g., http://www.javamex.com/tutorials/random_numbers/xorshift.shtml)
 * Not suitable as a source of randomness for cryptography. Not threadsafe.
 * <p>
 * For algo with better quality (longer period) but also not cryptographically secure, consider using a >=128 XOR-Shift,
 * see, e.g., https://www.codeproject.com/Articles/9187/A-fast-equivalent-for-System-Random
 */

public class XORShift32 extends java.util.Random {

    private long x;

    public XORShift32() {

        this(Optional.empty());

    }

    public XORShift32(Optional<Long> seedOpt) {

        x = seedOpt.orElse(System.nanoTime());

    }

    @Override
    public long nextLong() {

        x ^= (x << 21);

        x ^= (x >>> 35);

        x ^= (x << 4);

        return x;

    }

    public long nextPosLong() {

        return nextLong() & 0x7fffffffffffffffL;

    }

    @Override
    public int nextInt() {

        return (int) nextLong();

    }

    public int nextPosInt() {

        return nextInt() & 0x7fffffff;

    }

    @Override
    public int nextInt(int max) {

        return (int) (nextPosLong() / (0x7fffffffffffffffL / max + 1l));

        /* somewhat better quality? (better at avoiding bias in lower bits):

        int threshold = (0x7fffffff - max + 1) % max;

        for (;;) {

            int bits = (int) (nextLong() & 0x7fffffff);

            if (bits >= threshold)
                return bits % max;

        } */

    }

    @Override
    public float nextFloat() {

        return Math.scalb((float) (nextLong() & 0x7fffffffL), -31);

    }

    @Override
    public boolean nextBoolean() {

        return nextLong() >= 0l;

    }

    public double nextTriangular(double a, double b, double c) {

        double d = (c - a) / (b - a);

        double rand = nextDouble();

        if (rand < d)
            return a + Math.sqrt(rand * (b - a) * (c - a));
        else
            return b - Math.sqrt((1 - rand) * (b - a) * (b - c));

    }

}
