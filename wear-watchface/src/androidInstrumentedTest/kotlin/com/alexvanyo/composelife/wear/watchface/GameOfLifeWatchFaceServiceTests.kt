package com.alexvanyo.composelife.wear.watchface

import android.app.Application
import android.content.Intent
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Rect
import android.graphics.SurfaceTexture
import android.view.Surface
import android.view.SurfaceHolder
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.toIntRect
import androidx.core.graphics.get
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import androidx.wear.watchface.RenderParameters
import androidx.wear.watchface.WatchFaceService
import androidx.wear.watchface.client.DeviceConfig
import androidx.wear.watchface.client.WatchFaceControlClient
import androidx.wear.watchface.client.WatchUiState
import androidx.wear.watchface.complications.data.ComplicationData
import androidx.wear.watchface.control.WatchFaceControlService
import androidx.wear.watchface.style.UserStyleData
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.async
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.test.runTest
import kotlinx.datetime.Instant
import kotlinx.datetime.toJavaInstant
import org.junit.Assert.assertEquals
import org.junit.runner.RunWith
import kotlin.random.Random
import kotlin.test.Test

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
class GameOfLifeWatchFaceServiceTests {

    @Test
    fun test_no_user_style() = runTest {
        assertEquals(
            """
                |              X X    X                               X X    X         
                |   X   X           X                             X          X    X    
                |      X      X                                     X    X   X  XXX    
                |     X   X   X                                        X   X         XX
                |       X XX                                               X X X      X
                |         X   X                                                    X X 
                |X     X     X                                            X            
                | X     X                                                              
                | X    X   X                                                      X    
                | XX  X   X                                                            
                |  XX                                                               XX 
                |   X                                                                 X
                |X  XX X                                                               
                |  X X                                                           X     
                |                                                                    X 
                |                                                                    XX
                | X                                                                   X
                | X                                                                    
                |                                                                    X 
                |X                                                                    X
                |                                                                      
                |                                                                      
                |                                                                     X
                |X                                                                     
                |X                                                                     
                |                                                                      
                |                      XX XX X XX                XX    XX XX X XX      
                |                      XX X XX XX                XX    XX X XX XX      
                |                                                                      
                |                                                                      
                |                      XX                        XX    XX              
                |                      XX                        XX    XX              
                |                                   XX                                 
                |                                   XX                                 
                |                      XX X XX XX                XX    XX X XX XX      
                |                      XX XX X XX                XX    XX XX X XX      
                |                                   XX                                 
                |                                   XX                                 
                |                      XX      XX                XX            XX      
                |                      XX      XX                XX            XX      
                |                                                                      
                |                                                                      
                |                      XX XX X XX                XX    XX XX X XX      
                |                      XX X XX XX                XX    XX X XX XX      
                |                                                                      
                |                                                                      
                |                                                                      
                |                                                                     X
                |                                                                      
                | X                                                                    
                |                                                                     X
                |                                                                    X 
                |X                                                                     
                |XX X                                                              X X 
                |    X                                                                 
                |                                                                      
                |                                                                   X  
                |   X                                                           X XX XX
                |     XX                                                               
                |X    X                                                       X  X   X 
                | X X  XX                                                     X   X    
                |   X                                                       X  X       
                |X X                                                          X XX X   
                |      X   X                                                     X  XX 
                |  XX   X   X                                               XX   X X   
                | X  XX   X                                            X X    X     X  
                |  X    XX    X                                        X        X  XX  
                |      X   X   X X                                         X  X X     X
                |      XX   XX  X  X                                X X                
                |X         X      X      X      X     X   X                 XX   XX    
            """.trimMargin(),
            createOutput(
                instant = Instant.fromEpochMilliseconds(1675577751744L),
            )
        )
    }

    private val width = 70
    private val height = 70

    private val context = ApplicationProvider.getApplicationContext<Application>()

    private val surfaceTexture = SurfaceTexture(false)

    private val surface = Surface(surfaceTexture)

    private val surfaceHolder = object : SurfaceHolder {
        override fun addCallback(callback: SurfaceHolder.Callback?) = Unit

        override fun removeCallback(callback: SurfaceHolder.Callback?) = Unit

        override fun isCreating(): Boolean = error("Not implemented!")

        @Deprecated("Deprecated in Java", ReplaceWith("error(\"Not implemented!\")"))
        override fun setType(type: Int) = error("Not implemented!")

        override fun setFixedSize(width: Int, height: Int) = error("Not implemented!")

        override fun setSizeFromLayout() = error("Not implemented!")

        override fun setFormat(format: Int) = error("Not implemented!")

        override fun setKeepScreenOn(screenOn: Boolean) = error("Not implemented!")

        override fun lockCanvas(): Canvas = error("Not implemented!")

        override fun lockCanvas(dirty: Rect?): Canvas = lockCanvas()

        override fun unlockCanvasAndPost(canvas: Canvas?) = error("Not implemented!")

        override fun getSurfaceFrame(): Rect = IntSize(width, height).toIntRect().toAndroidRect()

        override fun getSurface(): Surface = this@GameOfLifeWatchFaceServiceTests.surface
    }

    private suspend fun createOutput(
        userStyle: UserStyleData? = null,
        deviceConfig: DeviceConfig = DeviceConfig(
            hasLowBitAmbient = false,
            hasBurnInProtection = false,
            analogPreviewReferenceTimeMillis = 0,
            digitalPreviewReferenceTimeMillis = 0
        ),
        watchUiState: WatchUiState = WatchUiState(false, 0),
        slotIdToComplicationData: Map<Int, ComplicationData>? = null,
        instant: Instant,
    ): String {
        val watchFaceService = DelegatingWatchFaceService(
            context = context,
            surfaceHolder = surfaceHolder,
        )

        watchFaceService.delegate.random = Random(0)

        val watchFaceControlService =
            WatchFaceControlClient.createWatchFaceControlClientImpl(
                context,
                Intent(context, WatchFaceControlService::class.java).apply {
                    action = WatchFaceControlService.ACTION_WATCHFACE_CONTROL_SERVICE
                }
            )

        val instance = coroutineScope {
            val instanceDeferred = async(Dispatchers.Main) {
                @Suppress("DEPRECATION")
                watchFaceControlService.getOrCreateInteractiveWatchFaceClient(
                    id = "testId",
                    deviceConfig = deviceConfig,
                    watchUiState = watchUiState,
                    userStyle = userStyle,
                    slotIdToComplicationData = slotIdToComplicationData,
                )
            }

            watchFaceService.onCreateEngine() as WatchFaceService.EngineWrapper

            instanceDeferred.await()
        }
        val bitmap = instance.renderWatchFaceToBitmap(
            renderParameters = RenderParameters.DEFAULT_INTERACTIVE,
            instant = instant.toJavaInstant(),
            userStyle = null,
            idAndComplicationData = null,
        )

        return (0 until bitmap.height).joinToString("\n") { y ->
            (0 until bitmap.width).joinToString("") { x ->
                when(bitmap[x, y]) {
                    Color.TRANSPARENT -> " "
                    else -> "X"
                }
            }
        }
    }
}
