//  THIS CODE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.

package utils;

import sun.misc.Unsafe;

import it.unimi.dsi.fastutil.ints.IntArrayList;


public class IntArrayUnsafe {

    public int size_;  // number of primitive int (4 byte) items

    public boolean isSorted = false;

    private long addr;

    static public Unsafe unsafe = null;  // see ByteArrayUnsafe for how to initialize

    private static long intArrayOffset = -1l;

    private static long alignment = -1l;

    private static long internalPadding = 1;  // multiple of alignment

    public boolean aligned = false;  // false avoids creation overhead for short-lived unsafe arrays

    public static void init(Unsafe us) {

        unsafe = us;

        intArrayOffset = unsafe.arrayBaseOffset(int[].class);

        alignment = unsafe.pageSize(); // for cache line size, use typically 64l

    }

    public IntArrayUnsafe(int size) {

        size_ = size;

        if (!aligned)
            addr = unsafe.allocateMemory(size << 2);
        else {

            addr = unsafe.allocateMemory((size << 2) + alignment + alignment * internalPadding);

            if (alignment > 0l && (addr & (alignment - 1l)) != 0)
                addr += (alignment - (addr & (alignment - 1)));

            addr += alignment * internalPadding;

        }

    }

    public IntArrayUnsafe(int[] values) {

        this(values.length);

        setFromIntArray(values);

    }

    public IntArrayUnsafe(IntArrayList values) {

        this(values.size());

        int i = -1;

        while (++i < size_)
            update(i, values.getInt((i)));

    }

    public void free() {

        unsafe.freeMemory(addr);

    }

    public int size() {

        return size_;

    }

    @Override
    public int hashCode() {

        int hashVal = 1;

        for (int i = 0; i < size_; i++)
            hashVal = 31 * hashVal + get(i);

        return hashVal;

    }

    @Override
    public boolean equals(Object obj) {

        if(!(obj instanceof IntArrayUnsafe) || ((IntArrayUnsafe) obj).size_ != size_)
            return false;

        if(isSorted) {

            for (int i = 0; i < size_; i++)
                if(((IntArrayUnsafe) obj).get(i) != get(i))
                    return false;

            return true;

        } else
            return java.util.Arrays.equals(toArray(), ((IntArrayUnsafe) obj).toArray());

    }

    public void setFromIntArray(int[] values) {

        long bytesToCopy = values.length << 2;

        unsafe.copyMemory(values, intArrayOffset,
                null, addr, bytesToCopy);

    }

    public void update(int index, int value) {

        unsafe.putInt(addr + (index << 2), value);

    }

    public void update(long index, int value) {

        unsafe.putInt(addr + (index << 2), value);

    }

    public int get(int index) {

        return unsafe.getInt(addr + (index << 2));

    }

    public int get(long index) {

        return unsafe.getInt(addr + (index << 2));

    }

    public int first() {

        return unsafe.getInt(addr);

    }

    public int second() {

        return unsafe.getInt(addr + 4);

    }

    public void inc(int index) {

        unsafe.getAndAddInt(null, addr + (index << 2), 1);

    }

    public int dec(int index) {

        return unsafe.getAndAddInt(null, addr + (index << 2), -1) - 1;

    }

    public void incBy(int index, int x) {

        unsafe.getAndAddInt(null, addr + (index << 2), x);

    }

    public void remove(int index) {

        unsafe.copyMemory(addr + ((index + 1) << 2), addr + (index << 2), (--size_ - index) << 2);

    }

    public int[] toArray() {

        //byte[] array = new byte[(int) size];  // note that an unsafe array can exceed Int.MaxValue size, in which case this would fail

        int[] array = new int[size_];

        unsafe.copyMemory(null, addr,
                array, intArrayOffset, size_ << 2);

        return array;

    }

    public int[] toArray(int l) {

        int[] array = new int[l];

        unsafe.copyMemory(null, addr,
                array, intArrayOffset,
                l << 2);

        return array;

    }

    public int[] toArray(int from, int until) {

        int[] array = new int[until - from];

        unsafe.copyMemory(null, addr + (from << 2),
                array, intArrayOffset,
                (until - from) << 2);

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

        unsafe.copyMemory(addr, bau.addr, size_ << 2);

        return bau;

    }

    public void distinctSorted() {

        // insertion sort, since our eli arrays are typically very small:

        int i = 1;

        while (i < size_) {

            int j = i;

            while (j > 0 && get(j - 1) > get(j)) {

                int h = get(j);

                update(j, get(j - 1));

                update(j - 1, h);

                j--;

            }

            i++;

        }

        // we remove duplicates:

        i = size_ - 1;

        while (i > 0 && i < size_) {

            if (get(i) == get(i - 1))
                remove(i - 1);
            else
                i--;

        }

    }

}
