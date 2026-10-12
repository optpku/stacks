/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Naturality
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.StrongTrans

/-!
# Absolute groupoid-fibred inertia transformations

Aggregate import for stable-universe forgetful and identity-section maps, their computations and
naturality, and strong pseudofunctor transformations. New clients can import `Maps` for
concrete transformation data, `Naturality` for direct and packaged laws, or `StrongTrans` for
coherence packaging. The typed owners are
`FiberedCategoryOver.Groupoids.Inertia.{forget,identitySection,forget.strongTrans,
identitySection.strongTrans}`.
-/

@[expose] public section
