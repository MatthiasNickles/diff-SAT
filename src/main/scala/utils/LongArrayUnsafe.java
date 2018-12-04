//  THIS CODE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.

package utils;

import sun.misc.Unsafe;

public class LongArrayUnsafe {

    private long size;  // number of primitive longs (8 byte)

    private long addr;

    public static Unsafe unsafe = null;  // see ByteArrayUnsafe for how to initialize

    private static long longArrayOffset = -1l;

    private static long alignment = -1l;

    private static long internalPadding = 1;  // multiple of alignment

    public static void init(Unsafe us) {

        unsafe = us;

        longArrayOffset = unsafe.arrayBaseOffset(long[].class);

        alignment = unsafe.pageSize(); // for cache line size, use typically 64l


    }

    public LongArrayUnsafe(long size, boolean aligned) {

        this.size = size;

        if(!aligned)
            addr = unsafe.allocateMemory(size << 3);
        else {

            addr = unsafe.allocateMemory((size << 3) + alignment + alignment * internalPadding);

            if (alignment > 0l && (addr & (alignment - 1l)) != 0)
                addr += (alignment - (addr & (alignment - 1)));

            addr += alignment * internalPadding;

        }

    }

    public LongArrayUnsafe(long size, long init, boolean aligned) {

        this(size, aligned);

        long i = size - 1;

        while (i >= 0l)
            update(i--, init);

    }

    public void free() {

        unsafe.freeMemory(addr);

    }

    public long size() {

        return size;

    }

    public void setFromIntArray(long[] values) {

        long bytesToCopy = values.length << 3;

        unsafe.copyMemory(values, longArrayOffset,
                null, addr, bytesToCopy);

    }

    public void update(int index, long value) {

        unsafe.putLong(addr + (index << 3), value);

    }

    public void update(long index, long value) {

        unsafe.putLong(addr + (index << 3), value);

    }

    public long get(long index) {

        return unsafe.getLong(addr + (index << 3));

    }

    /*public boolean contains(long item) {

        long i = size - 1;

        while (i >= 0l)
            if (get(i--) == item)
                return true;

        return false;

    }*/

    public long[] toArray() {  // TODO

        //byte[] array = new byte[(int) size];  // note that an unsafe array can exceed Int.MaxValue size, in which case this would fail

        long[] array = new long[(int) size];

        unsafe.copyMemory(null, addr,
                array, longArrayOffset, size << 3);

        return array;

    }

    public String toString() {

        StringBuilder s = new StringBuilder();

        for (long i = 0l; i < size; i++)
            s.append(i < size - 1l ? get(i) + "," : get(i));

        return s.toString();

    }

    public LongArrayUnsafe clone(long padding, boolean aligned) {

        LongArrayUnsafe bau = new LongArrayUnsafe(size + padding, aligned);

        unsafe.copyMemory(addr, bau.addr, size << 3);

        return bau;

    }

}
