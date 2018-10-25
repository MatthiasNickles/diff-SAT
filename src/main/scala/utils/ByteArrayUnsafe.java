
package utils;

import sun.misc.Unsafe;

import java.lang.reflect.Field;

public class ByteArrayUnsafe {

    private long size;

    private long address;

    private static Unsafe UNSAFE = null;

    private static long BYTE_ARRAY_OFFSET = -1l;

    public ByteArrayUnsafe(long size) {

        try {

            Field unsafeRefl = Unsafe.class.getDeclaredField("theUnsafe");

            unsafeRefl.setAccessible(true);

            UNSAFE = (Unsafe) unsafeRefl.get(null);

        } catch (Exception e) {

            System.err.println("Internal error: " + e);

        }

        BYTE_ARRAY_OFFSET = UNSAFE.arrayBaseOffset(byte[].class);

        this.size = size;

        address = UNSAFE.allocateMemory(size);


    }

    public void free() {

        UNSAFE.freeMemory(address);

    }

    public long size() {

        return size;

    }

    public void update(long i, byte value) {

        UNSAFE.putByte(address + i, value);

    }

    public void update(long i, boolean value) {

        UNSAFE.putByte(address + i, (byte) (value ? 0xFF : 0x00));

    }

    public byte get(long idx) {

        return UNSAFE.getByte(address + idx);

    }

    public boolean getBoolean(long idx) {

        return UNSAFE.getByte(address + idx) == (byte) 0xFF;

    }

    public byte[] toArray() {

        byte[] array = new byte[(int) size];  // note that an UNSAFE array can exceed Int.MaxValue size, in which case this would fail

        int si = 0;

        while (si < size) {

            array[si] = get(si);

            si++;

        }

        //UNSAFE.copyMemory(address, 0, array, BYTE_ARRAY_OFFSET, size); nope

        return array;

    }

    public ByteArrayUnsafe clone() {

        ByteArrayUnsafe bau = new ByteArrayUnsafe(size);

        UNSAFE.copyMemory(address, bau.address, size);

        return bau;

    }

    public void copyTo(ByteArrayUnsafe bau) {

        UNSAFE.copyMemory(address, bau.address, size);

    }

}
