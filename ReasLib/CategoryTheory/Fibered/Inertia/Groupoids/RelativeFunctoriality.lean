/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Map
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Naturality
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable

/-!
# Groupoid-fibred relative inertia functoriality

Compatibility aggregate for relative-to-absolute maps, functoriality of invertible squares,
their naturality comparison, and the stable-universe forgetful and section API. The typed
surface is owned directly by `FiberedCategoryOver.Groupoids.RelativeInertia`, notably
`{toInertia,map,forget,identitySection}` and `toInertia.naturalityIso`. Import a leaf module
directly when only one responsibility is needed.
-/

@[expose] public section
