/**
 * diff-SAT
 *
 * Copyright (c) 2018,2020 Matthias Nickles
 *
 * matthiasDOTnicklesATgmxDOTnet
 *
 * This code is licensed under MIT License (see file LICENSE for details).
 */

package input;

import com.sun.management.HotSpotDiagnosticMXBean;
import it.unimi.dsi.fastutil.objects.ReferenceArrayList;

import java.lang.management.ManagementFactory;
import java.lang.reflect.Field;
import java.util.Arrays;

import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;



import static org.apache.commons.math3.util.Precision.round;

public class UNSAFEhelper {

    public static final sun.misc.Unsafe UNSAFE;

    static AtomicLong allocatedOffHeapDiffSATGlobal = new AtomicLong(0l);

    public static final boolean debugMode = false;

    static ConcurrentHashMap<Long, String> allocs = null;  // for debugging only - don't use to trace off-heap space regularly!

    public static ReferenceArrayList<long[]> garbage = new ReferenceArrayList<>(); // (unclear whether stack access
    // via push/pop or queue access would be better - probably doesn't make much of a difference. But
    // use of ConcurrentLinkedQueue instead ReferenceArrayList is slower (if called with no or little concurrency anyway).
    // Important: we DON'T add anything to garbage during SAT solving. Only after all the core solver threads
    // have been stopped, we add memory addresses to garbage.

    static {

        if (debugMode) allocs = new ConcurrentHashMap<Long, String>();

    }

    static {

        try {

            Field field = sun.misc.Unsafe.class.getDeclaredField("theUnsafe");

            field.setAccessible(true);

            UNSAFE = (sun.misc.Unsafe) field.get(null);

        } catch (Throwable ex) {

            throw new ExceptionInInitializerError(ex);

        }

    }

    static long estimatedAvailableForUnsafe = Runtime.getRuntime().maxMemory();  // NB: this is what Java by default also allows for direct buffer allocations but
    // it tends to be an underestimate for the off-heap space available.  TODO: more accurate estimation wanted (without
    //  asking the OS or using Native Memory Tracking (NMT))

    static final HotSpotDiagnosticMXBean vmOptions = ManagementFactory.getPlatformMXBean(HotSpotDiagnosticMXBean.class);

    static {

        long maxDirectMemorySize = vmOptions == null ? 0l : Long.valueOf(vmOptions.getVMOption("MaxDirectMemorySize").getValue());

        // Observe that sun.misc.VM.maxDirectMemory() isn't available in recent JVMs.

        if (maxDirectMemorySize > 0l)
            estimatedAvailableForUnsafe = maxDirectMemorySize;

        if (debugMode)
            System.out.println("Off-heap memory estimate: " + approxSizeOfCurrentFreeUnsafeMemory() + " (" + Double.valueOf(approxSizeOfCurrentFreeUnsafeMemory()) / 1073741824d + " GB)");

    }

    static String formatCallerInfo(StackTraceElement[] stackStrace) {

        String callTreeStr = Arrays.toString(stackStrace);

        String callerInfo = callTreeStr;

        return callerInfo;

    }

    public static long allocateOffHeapMem(long size) {  // calling this method alone does NOT make it garbage collectable!

        allocatedOffHeapDiffSATGlobal.getAndAdd(size);

        if (debugMode) {

            long a = UNSAFE.allocateMemory(size);

            allocs.put(a, formatCallerInfo(new Throwable().fillInStackTrace().getStackTrace()));

            return a;

        } else
            return UNSAFE.allocateMemory(size);

    }

    public static long resizeOffHeapMem(long oldAddress, long oldSize, long newSize) {  // calling this method alone does NOT make it garbage collectable!

        allocatedOffHeapDiffSATGlobal.getAndAdd(-oldSize + newSize);

        if (debugMode) {

            long a = UNSAFE.reallocateMemory(oldAddress, newSize);

            allocs.remove(oldAddress);

            allocs.put(a, formatCallerInfo(new Throwable().fillInStackTrace().getStackTrace()));

            // System.out.println("FREED (by resize) " + oldAddress + ", bytes: " + oldSize + ", caller: " + callerInfo);

            // System.out.println("ALLOCATED (by resize) " + a + ", bytes: " + newSize + ", caller: " + callerInfo);

            return a;

        } else
            return UNSAFE.reallocateMemory(oldAddress, newSize);

    }

    public static void freeOffHeapMem(long address, long size) {

        allocatedOffHeapDiffSATGlobal.getAndAdd(-size);

        UNSAFE.freeMemory(address);

        if (debugMode) {

            allocs.remove(address);

            /* String callerInfo = formatCallerInfo(new Throwable().fillInStackTrace().getStackTrace())

             System.out.println("FREED " + address + ", bytes: " + size + ", caller: " + callerInfo);
            */

        }

    }

    public static void addAllocOffHeapMemToGarbage(long address, long size) {

        synchronized(garbage) {

            garbage.add(new long[]{address, size});

        }
    }

    public static void freeGarbageOffHeapMem(long targetMinBytesToFree) {

        synchronized(garbage) {

            long freed = 0l;

            if (targetMinBytesToFree > 0l && !garbage.isEmpty()) {

                if(debugMode) System.out.println("\nOff-heap garbage collection...");

                long f = 0l;

                do {

                    long[] entry = garbage.pop/*poll*/();

                    if(entry != null) {

                        freeOffHeapMem(entry[0], entry[1]);

                        f += entry[1];

                    }

                } while (freed < targetMinBytesToFree && !garbage.isEmpty());

                System.out.println("\n\u001B[35mOff-heap garbage collection complete. Freed " + f + " bytes (" + round(Float.valueOf(f) / 1073741824, 4) + " G)\u001B[0m");

                if (debugMode)
                    diffSAT.stats().writeEntry("offheapGarbageFreedBytes", f,  0, false);

            }

        }

    }

    public static long allocatedUnsafeMemory() {

        return allocatedOffHeapDiffSATGlobal.get();

    }

    /**
     * Accuracy depends on estimatedAvailableForUnsafe.
     *
     * @return Rough estimation of space originally (before any unsafe or direct buffer etc allocations) available for native allocations
     */
    public static long approxSizeOfInitialFreeUnsafeMemory() {

        return estimatedAvailableForUnsafe;

    }

    /**
     * Accuracy depends on estimatedAvailableForUnsafe. If this value is too low, we might even get a negative result.
     *
     * @return Rough estimation of space currently available for new native allocations
     */
    public static long approxSizeOfCurrentFreeUnsafeMemory() {

        return approxSizeOfInitialFreeUnsafeMemory() - allocatedUnsafeMemory();

    }

    /**
     * For debugging only. Don't call in code which uses this class concurrently
     */
    public static void resetMemTracerDebug() {

        allocatedOffHeapDiffSATGlobal.set(0l);

        if (debugMode) {

            allocs.clear();

        }

    }

    /**
     * For debugging, to find off-heap memory leaks
     */
    public static void showRemainingAllocsDebug() {

        if (debugMode) {

            if(allocs.isEmpty())
                System.out.println("No remaining items in off-heap garbage list for debugging");
            else  allocs.forEach((aLong, s) -> {

                if (true || !s.contains("LeanUS"))

                    System.out.println("REMAINING address (off-heap memory not freed by garbage collection):\n" + aLong + ", caller: " + s);

            });

        }

    }

}
