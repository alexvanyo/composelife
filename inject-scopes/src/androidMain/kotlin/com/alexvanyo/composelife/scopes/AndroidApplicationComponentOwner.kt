package com.alexvanyo.composelife.scopes

interface AndroidApplicationComponentOwner<AE, UE> : ApplicationComponentOwner<AE, AndroidUiComponentArguments, UE> {
    override val applicationComponent: AndroidApplicationComponent<AE>

    override val uiComponentFactory: (AndroidUiComponentArguments) -> AndroidUiComponent<AE, UE>
}
