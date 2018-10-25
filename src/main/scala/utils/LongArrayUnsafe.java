package utils;

import sun.misc.Unsafe;

public class LongArrayUnsafe {

    private long size;  // number of primitive long (8 byte) items

    private long address;

    public static Unsafe UNSAFE = null;

    private static long LONG_ARRAY_OFFSET = -1l;

    public static void init() {

        LONG_ARRAY_OFFSET = UNSAFE.arrayBaseOffset(long[].class);

    }

    public LongArrayUnsafe(long size) {

        this.size = size;

        address = UNSAFE.allocateMemory(size << 3);

    }

    public LongArrayUnsafe(long size, long init) {

        this.size = size;

        address = UNSAFE.allocateMemory(size << 3);

        long i = size - 1;

        while (i >= 0l)
            update(i--, init);

    }

    public void free() {

        UNSAFE.freeMemory(address);

    }

    public long size() {

        return size;

    }

    public void setFromIntArray(long[] values) {

        long bytesToCopy = values.length << 3;

        UNSAFE.copyMemory(values, LONG_ARRAY_OFFSET,
                null, address,
                bytesToCopy);

    }

    public void update(int i, long value) {

        UNSAFE.putLong(address + (i << 3), value);

    }

    public void update(long i, long value) {

        UNSAFE.putLong(address + (i << 3), value);

    }

    public long get(long i) {

        return UNSAFE.getLong(address + (i << 3));

    }

    public boolean contains(long item) {

        long i = size - 1;

        while (i >= 0l)
            if (get(i--) == item)
                return true;

        return false;

    }

    public long[] toArray() {  // TODO

        //byte[] array = new byte[(int) size];  // note that an UNSAFE array can exceed Int.MaxValue size, in which case this would fail

        long[] array = new long[(int) size];

        UNSAFE.copyMemory(null, address,
                array, LONG_ARRAY_OFFSET,
                size << 3);

        //UNSAFE.copyMemory(address, 0, array, BYTE_ARRAY_OFFSET, size); nope

        return array;

    }

    public String toString() {

        StringBuilder s = new StringBuilder();

        for (long i = 0l; i < size; i++)
            s.append(i < size - 1l ? get(i) + "," : get(i));

        return s.toString();

    }

    public LongArrayUnsafe clone(long padding) {

        LongArrayUnsafe bau = new LongArrayUnsafe(size + padding);

        UNSAFE.copyMemory(address, bau.address, size << 3);

        return bau;

    }

}
