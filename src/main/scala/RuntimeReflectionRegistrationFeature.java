/* Activate if native image generation using Graal is intended. Also see build.sbt and Target_scala_runtime_Statics.java

import com.oracle.svm.core.annotate.AutomaticFeature;
import org.graalvm.nativeimage.hosted.Feature;
import org.graalvm.nativeimage.hosted.RuntimeReflection;

import java.lang.reflect.Field;

// Tells Graal's native image generator about reflected fields in sharedDefs (otherwise this information
 // wouldn't be available anymore at delSAT runtime).
 // native-image.cmd must be called with argument  --features=RuntimeReflectionRegistrationFeature
@AutomaticFeature
public class RuntimeReflectionRegistrationFeature implements Feature {

    public void beforeAnalysis(BeforeAnalysisAccess access) {

        try {

            RuntimeReflection.register(sharedDefs.package$.class);

            Field[] paramFields = sharedDefs.package$.class.getDeclaredFields();

            for (int i = 0; i < paramFields.length; i++) {

                //System.out.println(">>" + paramFields[i].getName() + "<<");

                //RuntimeReflection.register(true,
                  //      sharedDefs.package$.class.getDeclaredField("abandonOrSwitchSlowThreads"));

                RuntimeReflection.register(sharedDefs.package$.class.getDeclaredField(paramFields[i].getName()));
                // NB: field must be var, not val in sharedDefs

            }


        } catch (Exception e) {

            System.err.println(e);

        }

    }

}

*/