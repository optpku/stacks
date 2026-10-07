module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Map
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Naturality
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Stable

/-!
# Setoid-fibred relative inertia functoriality

Aggregate for relative-to-absolute maps, square functoriality, stable-universe
forgetful and identity-section maps, and the canonical setoid-relative-inertia
equivalence. The typed surface is owned directly by
`FiberedCategoryOver.Setoids.RelativeInertia`, notably
`{toInertia,map,forget,identitySection,forget.equivalence}` and
`toInertia.naturalityIso`. Import a leaf module when only one responsibility is required.
-/

@[expose] public section
