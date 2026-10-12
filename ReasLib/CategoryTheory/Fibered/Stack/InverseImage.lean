/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward
public import ReasLib.CategoryTheory.Fibered.CategoryOver.CartesianHom
public import ReasLib.CategoryTheory.Fibered.Stack.Over
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse-image stacks

For a functor `u : C ⥤ D` representing a morphism of sites, an inverse-image stack of a stack
`X` over `(C, J)` is a stack over `(D, K)` equipped with an explicit pushforward projection and
a stackification comparison from the resulting source. This is stack infrastructure, not
gerbe-specific data.

## Main declarations

* `CategoryTheory.StackOver.inverseImageSource` — the bundled pushforward source.
* `CategoryTheory.StackOver.InverseImage` — a universe-polymorphic chosen inverse-image stack.
* `CategoryTheory.StackOver.InverseImage.source` — its explicitly certified source view.
* `CategoryTheory.StackOver.InverseImage.comparisonHom` — its fixed-universe comparison view.
-/

@[expose] public section

universe uC uD vC vD uS vS uT vT

namespace CategoryTheory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver

/-- Definition 8.12.9 (tag 04WJ): the fibred category over `D` obtained from an explicitly
chosen pushforward projection of the stack `X` along `u`. -/
@[stacks 04WJ]
noncomputable abbrev inverseImageSource (u : C ⥤ D) (X : StackOver.{uC, vC, uS, vS} J)
    (h : FiberedCategoryOver.Pushforward.ProjectionChoice u X.toFiberedCategoryOver) :
    FiberedCategoryOver D :=
  FiberedCategoryOver.pushforward u X.toFiberedCategoryOver h

/-- Definition 8.12.9 (tag 04WJ): the total category of the inverse-image source is the localized
pushforward category. -/
@[simp, stacks 04WJ "inverse-image source total category"]
theorem inverseImageSource.total (u : C ⥤ D) (X : StackOver.{uC, vC, uS, vS} J)
    (h : FiberedCategoryOver.Pushforward.ProjectionChoice u X.toFiberedCategoryOver) :
    (inverseImageSource u X h).total = Functor.pushforward u X.p := sorry

/-- Definition 8.12.9 (tag 04WJ): the projection of the inverse-image source is the localization
lifting selected by the explicit pushforward choice. -/
@[simp, stacks 04WJ "inverse-image source projection"]
theorem inverseImageSource.p (u : C ⥤ D) (X : StackOver.{uC, vC, uS, vS} J)
    (h : FiberedCategoryOver.Pushforward.ProjectionChoice u X.toFiberedCategoryOver) :
    (inverseImageSource u X h).p =
      Functor.Pushforward.projection u X.p h.inverts := sorry

/-- Definition 8.12.9 (tag 04WJ): an inverse-image stack of `X` along `u` is a target stack
over `(D, K)` equipped with an explicit pushforward source and a stackification comparison.
The source and target total categories may live in independent universes. -/
@[stacks 04WJ]
structure InverseImage (K : GrothendieckTopology D)
    (u : C ⥤ D) (X : StackOver.{uC, vC, uS, vS} J) where
  /-- The explicit projection choice used to form the pushforward source. -/
  sourceChoice : FiberedCategoryOver.Pushforward.ProjectionChoice
    u X.toFiberedCategoryOver
  /-- The target stack over `(D, K)`. -/
  target : StackOver.{uD, vD, uT, vT} K
  /-- The heterogeneous cartesian comparison from the explicitly chosen pushforward source to
  the target. -/
  comparison : CartesianBasedFunctor (inverseImageSource u X sourceChoice).p target.p
  /-- The comparison exhibits the target as a stackification. -/
  isStackification : CartesianBasedFunctor.IsStackification K comparison

attribute [stacks 04WJ "inverse-image source projection choice"]
  StackOver.InverseImage.sourceChoice
attribute [stacks 04WJ "inverse-image target stack choice"]
  StackOver.InverseImage.target
attribute [stacks 04WJ "inverse-image stackification comparison"]
  StackOver.InverseImage.comparison
attribute [stacks 04WJ "inverse-image stackification witness"]
  StackOver.InverseImage.isStackification

/- Axiom audit: `sourceChoice`, `target`, and `comparison` are explicit fields. The final field
is Prop-valued stackification evidence, so no non-Prop payload is synthesized from a proof. -/

/-- The explicitly chosen fibred pushforward source of an inverse-image stack. -/
@[stacks 04WJ "chosen inverse-image source"]
noncomputable abbrev InverseImage.source
    {u : C ⥤ D} {X : StackOver.{uC, vC, uS, vS} J}
    (I : InverseImage K u X) : FiberedCategoryOver D :=
  inverseImageSource u X I.sourceChoice

/-- The total category of the chosen inverse-image source is the localized pushforward
category. -/
@[simp, stacks 04WJ "chosen inverse-image source total category"]
theorem InverseImage.source.total
    {u : C ⥤ D} {X : StackOver.{uC, vC, uS, vS} J}
    (I : InverseImage K u X) :
    I.source.total = Functor.pushforward u X.p := sorry

/-- The projection of the chosen inverse-image source is the localization lifting selected by
`I.sourceChoice`. -/
@[simp, stacks 04WJ "chosen inverse-image source projection"]
theorem InverseImage.source.p
    {u : C ⥤ D} {X : StackOver.{uC, vC, uS, vS} J}
    (I : InverseImage K u X) :
    I.source.p = Functor.Pushforward.projection u X.p I.sourceChoice.inverts := sorry

namespace InverseImage

/-- Regard the heterogeneous comparison as a morphism in the fixed fibred-category bicategory
when the chosen target lives in the source's total-category universes. -/
@[stacks 04WJ "fixed-universe inverse-image comparison"]
noncomputable def comparisonHom
    {u : C ⥤ D} {X : StackOver.{uC, vC, uS, vS} J}
    (I : InverseImage K u X) : I.source ⟶ I.target.toFiberedCategoryOver :=
  (FiberedCategoryOver.CartesianHom.toHom I.source I.target.toFiberedCategoryOver).obj
    I.comparison

/-- Forgetting the fixed-universe comparison recovers the canonical heterogeneous comparison. -/
@[simp, stacks 04WJ "underlying inverse-image comparison"]
theorem comparisonHom.toCartesianBasedFunctor
    {u : C ⥤ D} {X : StackOver.{uC, vC, uS, vS} J}
    (I : InverseImage K u X) :
    FiberedCategoryOver.toCartesianBasedFunctor I.comparisonHom = I.comparison := sorry

/-- The fixed-universe comparison view remains a stackification. -/
@[stacks 04WJ "fixed-universe inverse-image comparison is a stackification"]
theorem comparisonHom.isStackification
    {u : C ⥤ D} {X : StackOver.{uC, vC, uS, vS} J}
    (I : InverseImage K u X) :
    FiberedCategoryOver.Hom.IsStackification K I.comparisonHom := sorry

end InverseImage

end StackOver

end CategoryTheory
