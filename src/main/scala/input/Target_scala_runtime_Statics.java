package input;

// Activate if native image generation using Graal is intended.
// !!! Also see build.sbt and RuntimeReflectionRegistrationFeature.java !!!

// For native diff-SAT image creation using GraalVM 20.0 (see https://github.com/scala/bug/issues/11634)
// Requires libraryDependencies += "com.oracle.substratevm" % "svm" % "19.2.1" % Provided in build.sbt

import com.oracle.svm.core.annotate.*;

@TargetClass(className = "scala.runtime.Statics")
final class Target_scala_runtime_Statics {

    @Substitute
    public static void releaseFence() {
        UNSAFEhelper.UNSAFE.storeFence();
    }

}

