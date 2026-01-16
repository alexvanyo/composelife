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

-dontwarn android.view.accessibility.AccessibilityNodeInfo$Selection
-dontwarn android.view.accessibility.AccessibilityNodeInfo$SelectionPosition

-dontwarn androidx.fragment.app.Fragment
-dontwarn androidx.fragment.app.FragmentActivity
-dontwarn androidx.fragment.app.FragmentManager$FragmentLifecycleCallbacks
-dontwarn androidx.fragment.app.FragmentManager
-dontwarn androidx.fragment.app.FragmentTransitionImpl
-dontwarn androidx.test.platform.app.AppComponentFactoryRegistry
-dontwarn androidx.test.platform.concurrent.DirectExecutor
-dontwarn androidx.window.extensions.WindowExtensions
-dontwarn androidx.window.extensions.WindowExtensionsProvider
-dontwarn androidx.window.extensions.area.ExtensionWindowAreaPresentation
-dontwarn androidx.window.extensions.area.ExtensionWindowAreaStatus
-dontwarn androidx.window.extensions.area.WindowAreaComponent
-dontwarn androidx.window.extensions.core.util.function.Consumer
-dontwarn androidx.window.extensions.core.util.function.Function
-dontwarn androidx.window.extensions.core.util.function.Predicate
-dontwarn androidx.window.extensions.embedding.ActivityEmbeddingComponent
-dontwarn androidx.window.extensions.embedding.ActivityRule$Builder
-dontwarn androidx.window.extensions.embedding.ActivityRule
-dontwarn androidx.window.extensions.embedding.ActivityStack$Token
-dontwarn androidx.window.extensions.embedding.ActivityStack
-dontwarn androidx.window.extensions.embedding.ActivityStackAttributes$Builder
-dontwarn androidx.window.extensions.embedding.ActivityStackAttributes
-dontwarn androidx.window.extensions.embedding.ActivityStackAttributesCalculatorParams
-dontwarn androidx.window.extensions.embedding.AnimationBackground$ColorBackground
-dontwarn androidx.window.extensions.embedding.AnimationBackground
-dontwarn androidx.window.extensions.embedding.AnimationParams$Builder
-dontwarn androidx.window.extensions.embedding.AnimationParams
-dontwarn androidx.window.extensions.embedding.DividerAttributes$Builder
-dontwarn androidx.window.extensions.embedding.DividerAttributes
-dontwarn androidx.window.extensions.embedding.EmbeddedActivityWindowInfo
-dontwarn androidx.window.extensions.embedding.EmbeddingRule
-dontwarn androidx.window.extensions.embedding.ParentContainerInfo
-dontwarn androidx.window.extensions.embedding.SplitAttributes$Builder
-dontwarn androidx.window.extensions.embedding.SplitAttributes$SplitType$ExpandContainersSplitType
-dontwarn androidx.window.extensions.embedding.SplitAttributes$SplitType$HingeSplitType
-dontwarn androidx.window.extensions.embedding.SplitAttributes$SplitType$RatioSplitType
-dontwarn androidx.window.extensions.embedding.SplitAttributes$SplitType
-dontwarn androidx.window.extensions.embedding.SplitAttributes
-dontwarn androidx.window.extensions.embedding.SplitAttributesCalculatorParams
-dontwarn androidx.window.extensions.embedding.SplitInfo$Token
-dontwarn androidx.window.extensions.embedding.SplitInfo
-dontwarn androidx.window.extensions.embedding.SplitPairRule$Builder
-dontwarn androidx.window.extensions.embedding.SplitPairRule
-dontwarn androidx.window.extensions.embedding.SplitPinRule$Builder
-dontwarn androidx.window.extensions.embedding.SplitPinRule
-dontwarn androidx.window.extensions.embedding.SplitPlaceholderRule$Builder
-dontwarn androidx.window.extensions.embedding.SplitPlaceholderRule
-dontwarn androidx.window.extensions.embedding.SplitRule
-dontwarn androidx.window.extensions.embedding.WindowAttributes
-dontwarn androidx.window.extensions.layout.DisplayFeature
-dontwarn androidx.window.extensions.layout.DisplayFoldFeature
-dontwarn androidx.window.extensions.layout.FoldingFeature
-dontwarn androidx.window.extensions.layout.SupportedWindowFeatures
-dontwarn androidx.window.extensions.layout.WindowLayoutComponent
-dontwarn androidx.window.extensions.layout.WindowLayoutInfo
-dontwarn androidx.window.sidecar.SidecarDeviceState
-dontwarn androidx.window.sidecar.SidecarDisplayFeature
-dontwarn androidx.window.sidecar.SidecarInterface$SidecarCallback
-dontwarn androidx.window.sidecar.SidecarInterface
-dontwarn androidx.window.sidecar.SidecarProvider
-dontwarn androidx.window.sidecar.SidecarWindowLayoutInfo
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
-dontwarn javax.inject.Qualifier
-dontwarn javax.inject.Scope
-dontwarn javax.lang.model.element.Modifier
