package utils;

/**
 * Fast but low-quality random numbers using a basic XOR-shift algorithm (http://www.javamex.com/tutorials/random_numbers/xorshift.shtml)
 * Not threadsafe.
 * <p>
 * For better quality (longer period), consider using a >=128 XOR-Shift, e.g.,
 * https://www.codeproject.com/Articles/9187/A-fast-equivalent-for-System-Random
 */

public class XORShift32 extends java.util.Random {

    private long x;

    public XORShift32() {

        x = System.nanoTime();

    }

    public XORShift32(long seed) {

        x = seed;

    }

    @Override public long nextLong() {

        x ^= (x << 21);

        x ^= (x >>> 35);

        x ^= (x << 4);

        return x;

    }

    public long nextPosLong() {

        return nextLong() & 0x7fffffffffffffffL;

    }

    @Override public int nextInt() {

        return (int) nextLong();

    }

    @Override public int nextInt(int max) {

        return (int) (nextPosLong() / (0x7fffffffffffffffL / max + 1l));

        /* somewhat better quality (better at avoiding bias in lower bits):

        int threshold = (0x7fffffff - max + 1) % max;

        for (;;) {

            int bits = (int) (nextLong() & 0x7fffffff);

            if (bits >= threshold)
                return bits % max;

        } */

    }

    @Override  public float nextFloat() {

        return Math.scalb((float) (nextLong() & 0x7fffffffL), -31);

    }

    @Override public boolean nextBoolean() {

        return nextLong() >= 0l;

    }

}
