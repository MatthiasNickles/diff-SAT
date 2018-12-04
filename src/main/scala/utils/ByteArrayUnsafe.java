//  THIS CODE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.

package utils;

import java.lang.reflect.Field;

import sun.misc.Unsafe;

public class ByteArrayUnsafe {

    private long size;

    private long addr;

    private static Unsafe unsafe = null;

    private static long byteArrayUnsafe = -1l;

    public ByteArrayUnsafe(long size) {

        try {

            Field unsafeViaReflection = Unsafe.class.getDeclaredField("theUnsafe");

            unsafeViaReflection.setAccessible(true);

            unsafe = (Unsafe) unsafeViaReflection.get(null);

        } catch (Exception e) {

            System.err.println("Internal error: " + e);

        }

        byteArrayUnsafe = unsafe.arrayBaseOffset(byte[].class);

        this.size = size;

        addr = unsafe.allocateMemory(size);

    }

    public long size() {

        return size;

    }

    public void free() {

        unsafe.freeMemory(addr);

    }

    public void update(long i, byte value) {

        unsafe.putByte(addr + i, value);

    }

    public void update(long i, boolean value) {

        unsafe.putByte(addr + i, (byte) (value ? 0xFF : 0x00));

    }

    public boolean getBoolean(long index) {

        return unsafe.getByte(addr + index) == (byte) 0xFF;

    }

    public byte get(long index) {

        return unsafe.getByte(addr + index);

    }

    public byte[] toArray() {

        byte[] array = new byte[(int) size];  // note that an unsafe array can exceed Int.MaxValue size, in which case this would fail

        int si = 0;

        while (si < size) {

            array[si] = get(si);

            si++;

        }

        //unsafe.copyMemory(addr, 0, array, byteArrayUnsafe, size); nope

        return array;

    }

    public ByteArrayUnsafe clone() {

        ByteArrayUnsafe bau = new ByteArrayUnsafe(size);

        unsafe.copyMemory(addr, bau.addr, size);

        return bau;

    }

    public void copyTo(ByteArrayUnsafe a) {

        unsafe.copyMemory(addr, a.addr, size);

    }

}
