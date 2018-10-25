
package utils;

import sun.misc.Unsafe;

import java.lang.reflect.Field;

public class IntArrayUnsafe {

    public int size_;  // number of primitive int (4 byte) items

    private long address;

    static public Unsafe UNSAFE = null;

    //private static long BYTE_ARRAY_OFFSET = -1l;

    private static long INT_ARRAY_OFFSET = -1l;

    public static void init() {

        INT_ARRAY_OFFSET = UNSAFE.arrayBaseOffset(int[].class);

    }

    public IntArrayUnsafe(int size) {

        size_ = size;

        address = UNSAFE.allocateMemory(size << 2);

    }

    public void free() {

        UNSAFE.freeMemory(address);

    }

    public int size() {

        return size_;

    }

    public void setFromIntArray(int[] values) {

        long bytesToCopy = values.length << 2;

        UNSAFE.copyMemory(values, INT_ARRAY_OFFSET,
                null, address,
                bytesToCopy);

    }

    public void update(int i, int value) {

        UNSAFE.putInt(address + (i << 2), value);

    }

    public void update(long i, int value) {

        UNSAFE.putInt(address + (i << 2), value);

    }

    public int get(long i) {

        return UNSAFE.getInt(address + (i << 2));

    }

    public int first() {

        return UNSAFE.getInt(address);

    }

    public int second() {

        return UNSAFE.getInt(address + 4);

    }

    public int get(int i) {

        return UNSAFE.getInt(address + (i << 2));

    }

    public void inc(int i) {

        UNSAFE.getAndAddInt(null, address + (i << 2), 1);

    }

    public void incBy(int i, int x) {

        UNSAFE.getAndAddInt(null, address + (i << 2), x);

    }

    public int dec(int i) {

        return UNSAFE.getAndAddInt(null, address + (i << 2), -1) - 1;

    }


    public void remove(int i) {

        UNSAFE.copyMemory(address + ((i + 1) << 2), address + (i << 2), (--size_ - i) << 2);

    }


    public int[] toArray() {

        //byte[] array = new byte[(int) size];  // note that an UNSAFE array can exceed Int.MaxValue size, in which case this would fail

        int[] array = new int[size_];

        UNSAFE.copyMemory(null, address,
                array, INT_ARRAY_OFFSET,
                size_ << 2);

        //UNSAFE.copyMemory(address, 0, array, BYTE_ARRAY_OFFSET, size_); nope

        return array;

    }

    public int[] toArray(int l) {

        int[] array = new int[l];

        UNSAFE.copyMemory(null, address,
                array, INT_ARRAY_OFFSET,
                l << 2);

        return array;

    }

    public String toString() {

        StringBuilder s = new StringBuilder();

        for (int i = 0; i < size_; i++)
            s.append(i < size_ - 1 ? get(i) + "," : get(i));

        return s.toString();

    }

    public IntArrayUnsafe clone(int padding) {

        IntArrayUnsafe bau = new IntArrayUnsafe(size_ + padding);

        UNSAFE.copyMemory(address, bau.address, size_ << 2);

        return bau;

    }

}
