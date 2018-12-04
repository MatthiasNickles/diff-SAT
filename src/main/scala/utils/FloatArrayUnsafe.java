//  THIS CODE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.

package utils;

import sun.misc.Unsafe;

public class FloatArrayUnsafe {

    public int size_;  // number of primitive int (4 byte) items

    private long addr;

    static public Unsafe unsafe = null;  // see ByteArrayUnsafe for how to initialize

    private static long floatArrayOffset = -1l;

    private static long alignment = -1l;

    private static long internalPadding = 1;  // multiple of alignment

    public static void init(Unsafe us) {

        unsafe = us;

        floatArrayOffset = unsafe.arrayBaseOffset(int[].class);

        alignment = unsafe.pageSize(); // for cache line size, use typically 64l

    }

    public FloatArrayUnsafe(int size, boolean aligned) {

        size_ = size;

        if(!aligned)
            addr = unsafe.allocateMemory(size << 2);
        else {

            addr = unsafe.allocateMemory((size << 2) + alignment + alignment * internalPadding);

            if (alignment > 0l && (addr & (alignment - 1l)) != 0)
                addr += (alignment - (addr & (alignment - 1)));

            addr += alignment * internalPadding;

        }

    }

    public FloatArrayUnsafe(float[] values, boolean aligned) {

        this(values.length, aligned);

        setFromIntArray(values);

    }


    public void free() {

        unsafe.freeMemory(addr);

    }

    public int size() {

        return size_;

    }

    public void setFromIntArray(float[] values) {

        long bytesToCopy = values.length << 2;

        unsafe.copyMemory(values, floatArrayOffset,
                null, addr, bytesToCopy);

    }

    public void update(int index, float value) {

        unsafe.putFloat(addr + (index << 2), value);

    }

    public void update(long index, float value) {

        unsafe.putFloat(addr + (index << 2), value);

    }

    public float get(int index) {

        return unsafe.getFloat(addr + (index << 2));

    }

    public float get(long index) {

        return unsafe.getFloat(addr + (index << 2));

    }

    public float first() {

        return unsafe.getFloat(addr);

    }

    public float second() {

        return unsafe.getFloat(addr + 4);

    }


    public void remove(int index) {

        unsafe.copyMemory(addr + ((index + 1) << 2), addr + (index << 2), (--size_ - index) << 2);

    }

    public float[] toArray() {

        float[] array = new float[size_];

        unsafe.copyMemory(null, addr,
                array, floatArrayOffset, size_ << 2);

        return array;

    }

    public float[] toArray(int l) {

        float[] array = new float[l];

        unsafe.copyMemory(null, addr,
                array, floatArrayOffset,
                l << 2);

        return array;

    }

    public float[] toArray(int from, int until) {

        float[] array = new float[until - from];

        unsafe.copyMemory(null, addr + (from << 2),
                array, floatArrayOffset,
                (until - from) << 2);

        return array;

    }

    public String toString() {

        StringBuilder s = new StringBuilder();

        for (int i = 0; i < size_; i++)
            s.append(i < size_ - 1 ? get(i) + "," : get(i));

        return s.toString();

    }

    public FloatArrayUnsafe clone(int padding, boolean aligned) {

        FloatArrayUnsafe bau = new FloatArrayUnsafe(size_ + padding, aligned);

        unsafe.copyMemory(addr, bau.addr, size_ << 2);

        return bau;

    }

}
