# parameterized-string

A small utility module that allows recursively defining a string resource or quantity string
resource, which may have other resources defined.

This allows a nice way to separate the definition of a string resource (which might be done at a
deeper layer in the app) from the resolution of the string resource (which must be done in the UI
layer, as explored [here](https://medium.com/androiddevelopers/locale-changes-and-the-androidviewmodel-antipattern-84eb677660d9))
