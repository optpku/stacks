module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Map
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Target
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
theorem comparisonTargetIsoApp_naturality
    (X : FiberedCategoryOver.Groupoids C)
    {x y : X.total} (f : x ⟶ y) :
    (PseudoPullbackComparison.target
        (PseudoPullbackCone.diagonal X.baseProjection)).map f ≫
        (comparisonTargetIsoApp X y).hom =
      (comparisonTargetIsoApp X x).hom ≫
        (Δₚ X.p).map f := sorry

end Implementation

set_option backward.privateInPublic true in
/- The categorical-pullback target of the generic diagonal cone is explicitly naturally
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

/-- The morphism from the diagonal cone to the two-fibre-product cone whose apex map is the
canonical diagonal itself. Its comparison uses the same identity components as that diagonal. -/
@[stacks 0H2E "canonical diagonal cone comparison"]
noncomputable def coneComparison
    (X : FiberedCategoryOver.Groupoids C) :
    PseudoPullbackCone.diagonal X.baseProjection ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection :=
  PseudoPullbackCone.homMk
    (FiberedCategoryOver.Groupoids.diagonal X)
    (Hom.diagonal.comparisonIso X.baseProjection).hom

namespace Implementation

/-- The actual diagonal has the identity comparison on its two equal entries. -/
private theorem toCategoricalPullbackIsoApp_w
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    X.p.map (𝟙 x) ≫ ((Δₚ X.p).obj x).iso.hom =
      ((PseudoPullbackComparison.map (FiberedCategoryOver.Groupoids.diagonal X)).obj x).iso.hom ≫
        X.p.map (𝟙 x) := sorry

/-- Both legs of the diagonal comparison are actual identity isomorphisms. -/
private noncomputable def toCategoricalPullbackIsoApp
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    (PseudoPullbackComparison.map (FiberedCategoryOver.Groupoids.diagonal X)).obj x ≅
      (Δₚ X.p).obj x :=
  CategoricalPullback.mkIso
    (Iso.refl x) (Iso.refl x)
    (toCategoricalPullbackIsoApp_w X x)

/-- The identity-pair comparison is natural in the original total-category arrows. -/
theorem toCategoricalPullbackIsoApp_naturality
    (X : FiberedCategoryOver.Groupoids C)
    {x y : X.total} (f : x ⟶ y) :
    (PseudoPullbackComparison.map (FiberedCategoryOver.Groupoids.diagonal X)).map f ≫
        (toCategoricalPullbackIsoApp X y).hom =
      (toCategoricalPullbackIsoApp X x).hom ≫ (Δₚ X.p).map f := sorry

end Implementation

set_option backward.privateInPublic true in
/- Under the explicit Remark-4.35.8 equivalence, the canonical relative diagonal is the ordinary
categorical-pullback diagonal. The comparison and its inverse use identity components on both
entries of the actual diagonal object. -/
@[stacks 0H2E "canonical relative diagonal as a categorical diagonal"]
noncomputable def toCategoricalPullbackIso
    (X : FiberedCategoryOver.Groupoids C) :
    PseudoPullbackComparison.map
        (FiberedCategoryOver.Groupoids.diagonal X) ≅
      Δₚ X.p :=
  NatIso.ofComponents
    (Implementation.toCategoricalPullbackIsoApp X)
    (fun f ↦ Implementation.toCategoricalPullbackIsoApp_naturality X f)

/-- The first forward component of the relative-diagonal comparison is the identity. -/
@[simp]
theorem toCategoricalPullbackIso.hom.app.fst
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((toCategoricalPullbackIso X).hom.app x).fst = 𝟙 x := sorry

/-- The second forward component of the relative-diagonal comparison is the identity. -/
@[simp]
theorem toCategoricalPullbackIso.hom.app.snd
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((toCategoricalPullbackIso X).hom.app x).snd = 𝟙 x := sorry

/-- The first inverse component of the relative-diagonal comparison is the identity. -/
@[simp]
theorem toCategoricalPullbackIso.inv.app.fst
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((toCategoricalPullbackIso X).inv.app x).fst = 𝟙 x := sorry

/-- The second inverse component of the relative-diagonal comparison is the identity. -/
@[simp]
theorem toCategoricalPullbackIso.inv.app.snd
    (X : FiberedCategoryOver.Groupoids C) (x : X.total) :
    ((toCategoricalPullbackIso X).inv.app x).snd = 𝟙 x := sorry
end FiberedCategoryOver.Groupoids.Diagonal

end CategoryTheory
