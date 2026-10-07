module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Iso
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal

/-!
# Diagonal target comparison

This leaf identifies the pseudo-pullback comparison target of the generic
fibred diagonal with the ordinary categorical diagonal.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.Diagonal

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The categorical-pullback functor attached to the generic diagonal cone is the ordinary
categorical diagonal. -/
theorem comparisonTarget.eq
    (X : FiberedCategoryOver.Groupoids C) :
    PseudoPullbackComparison.target (PseudoPullbackCone.diagonal X.baseProjection) = Δₚ X.p := sorry
/- Proof strategy: unfold `PseudoPullbackComparison.target`, `PseudoPullbackCone.diagonal`, and `Δₚ`;
both functors have identical object and morphism data. -/

namespace Implementation

/-- Compatibility of the identity component isomorphisms comparing the categorical-pullback
target of the diagonal cone with the ordinary diagonal object. -/
private theorem comparisonTargetIsoApp_w
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    X.p.map (𝟙 x) ≫ ((Δₚ X.p).obj x).iso.hom =
      (PseudoPullbackComparison.target
          (PseudoPullbackCone.diagonal X.baseProjection) |>.obj x).iso.hom ≫
        X.p.map (𝟙 x) := sorry

/-- The objectwise comparison from the categorical-pullback target of the diagonal cone to the
ordinary diagonal. Its two non-Prop leg components are identities. -/
private noncomputable def comparisonTargetIsoApp
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    (PseudoPullbackComparison.target
        (PseudoPullbackCone.diagonal X.baseProjection)).obj x ≅
      (Δₚ X.p).obj x :=
  CategoricalPullback.mkIso
    (Iso.refl x) (Iso.refl x)
    (comparisonTargetIsoApp_w X x)

/-- The explicit diagonal-target comparisons are natural in total-category morphisms. -/
private theorem comparisonTargetIsoApp_naturality
    (X : FiberedCategoryOver.Groupoids C)
    {x y : X.total} (f : x ⟶ y) :
    (PseudoPullbackComparison.target
        (PseudoPullbackCone.diagonal X.baseProjection)).map f ≫
        (comparisonTargetIsoApp X y).hom =
      (comparisonTargetIsoApp X x).hom ≫
        (Δₚ X.p).map f := sorry

end Implementation

/-- The categorical-pullback target of the generic diagonal cone is explicitly naturally
isomorphic to the ordinary categorical diagonal. -/
@[stacks 0H2E "categorical target of the diagonal comparison"]
noncomputable def comparisonTargetIso
    (X : FiberedCategoryOver.Groupoids C) :
    PseudoPullbackComparison.target
        (PseudoPullbackCone.diagonal X.baseProjection) ≅
      Δₚ X.p :=
  NatIso.ofComponents
    (Implementation.comparisonTargetIsoApp X)
    (fun f ↦ Implementation.comparisonTargetIsoApp_naturality X f)

/-- The first component of the forward diagonal-target comparison is the identity. -/
@[simp]
theorem comparisonTargetIso.hom.app.fst
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((comparisonTargetIso X).hom.app x).fst = 𝟙 x := sorry

/-- The second component of the forward diagonal-target comparison is the identity. -/
@[simp]
theorem comparisonTargetIso.hom.app.snd
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((comparisonTargetIso X).hom.app x).snd = 𝟙 x := sorry

/-- The first component of the inverse diagonal-target comparison is the identity. -/
@[simp]
theorem comparisonTargetIso.inv.app.fst
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((comparisonTargetIso X).inv.app x).fst = 𝟙 x := sorry

/-- The second component of the inverse diagonal-target comparison is the identity. -/
@[simp]
theorem comparisonTargetIso.inv.app.snd
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((comparisonTargetIso X).inv.app x).snd = 𝟙 x := sorry

/-- The canonical morphism from the diagonal pseudo-pullback cone to the chosen
two-fibre-product cone. Naming this concrete datum keeps downstream comparisons independent of
the implementation of `PseudoPullbackCone.homMk`. -/
@[stacks 0H2E "canonical diagonal cone comparison"]
noncomputable def coneComparison
    (X : FiberedCategoryOver.Groupoids C) :
    PseudoPullbackCone.diagonal X.baseProjection ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection :=
  PseudoPullbackCone.lift.hom
    (PseudoPullbackCone.diagonal X.baseProjection)
    (CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)

/-- Under the explicit Remark-4.35.8 equivalence, the canonical relative diagonal is the ordinary
categorical-pullback diagonal. The construction uses its universal comparison isomorphism, not
definitional equality with a concrete pullback implementation. -/
@[stacks 0H2E "canonical relative diagonal as a categorical diagonal"]
noncomputable def toCategoricalPullbackIso
    (X : FiberedCategoryOver.Groupoids C) :
    PseudoPullbackComparison.map
        (FiberedCategoryOver.Groupoids.diagonal X) ≅
      Δₚ X.p :=
  PseudoPullbackComparison.iso (coneComparison X) ≪≫
    comparisonTargetIso X

/-- The first forward component of the canonical relative-diagonal comparison is the first
component of the universal pseudo-pullback leg comparison. -/
@[simp]
theorem toCategoricalPullbackIso.hom.app.fst
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((toCategoricalPullbackIso X).hom.app x).fst =
      (PseudoPullbackComparison.fstIso (coneComparison X)).hom.app x := sorry

/-- The second forward component of the canonical relative-diagonal comparison is the second
component of the universal pseudo-pullback leg comparison. -/
@[simp]
theorem toCategoricalPullbackIso.hom.app.snd
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((toCategoricalPullbackIso X).hom.app x).snd =
      (PseudoPullbackComparison.sndIso (coneComparison X)).hom.app x := sorry

/-- The first inverse component of the canonical relative-diagonal comparison is the first
component of the inverse universal pseudo-pullback leg comparison. -/
@[simp]
theorem toCategoricalPullbackIso.inv.app.fst
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((toCategoricalPullbackIso X).inv.app x).fst =
      (PseudoPullbackComparison.fstIso (coneComparison X)).inv.app x := sorry

/-- The second inverse component of the canonical relative-diagonal comparison is the second
component of the inverse universal pseudo-pullback leg comparison. -/
@[simp]
theorem toCategoricalPullbackIso.inv.app.snd
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((toCategoricalPullbackIso X).inv.app x).snd =
      (PseudoPullbackComparison.sndIso (coneComparison X)).inv.app x := sorry
end FiberedCategoryOver.Groupoids.Diagonal

end CategoryTheory
