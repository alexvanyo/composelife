# Add project specific ProGuard rules here.
# You can control the set of applied configuration files using the
# proguardFiles setting in build.gradle.kts.
#
# For more details, see
#   http://developer.android.com/guide/developing/tools/proguard.html

# If your project uses WebView with JS, uncomment the following
# and specify the fully qualified class name to the JavaScript interface
# class:
#-keepclassmembers class fqcn.of.javascript.interface.for.webview {
#   public *;
#}

# Uncomment this to preserve the line number information for
# debugging stack traces.
#-keepattributes SourceFile,LineNumberTable

# If you keep the line number information, uncomment this to
# hide the original source file name.
#-renamesourcefileattribute SourceFile

# Added due to dependency on Material via accessibility-test-framework
-dontwarn androidx.appcompat.graphics.drawable.DrawableWrapper

-dontwarn androidx.test.platform.app.AppComponentFactoryRegistry
-dontwarn androidx.test.platform.concurrent.DirectExecutor
-dontwarn androidx.work.Data$Builder
-dontwarn androidx.work.Data
-dontwarn androidx.work.ForegroundInfo
-dontwarn androidx.work.ListenableWorker$Result
-dontwarn androidx.work.OneTimeWorkRequest$Builder
-dontwarn androidx.work.OneTimeWorkRequest
-dontwarn androidx.work.Operation
-dontwarn androidx.work.OutOfQuotaPolicy
-dontwarn androidx.work.WorkManager
-dontwarn androidx.work.WorkRequest$Builder
-dontwarn androidx.work.WorkRequest
-dontwarn androidx.work.Worker
-dontwarn androidx.work.WorkerParameters
-dontwarn androidx.work.impl.utils.futures.SettableFuture
-dontwarn androidx.work.multiprocess.RemoteListenableWorker
-dontwarn java.beans.BeanInfo
-dontwarn java.beans.FeatureDescriptor
-dontwarn java.beans.IntrospectionException
-dontwarn java.beans.Introspector
-dontwarn java.beans.PropertyDescriptor
-dontwarn java.lang.reflect.AnnotatedType
-dontwarn javax.lang.model.element.Modifier
