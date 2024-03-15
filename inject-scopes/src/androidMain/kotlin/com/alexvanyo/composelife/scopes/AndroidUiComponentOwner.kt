package com.alexvanyo.composelife.scopes

interface AndroidUiComponentOwner<T : AndroidApplicationComponent<E>, E> : UiComponentOwner {
    override val uiComponent: AndroidUiComponent<T, E>
}
