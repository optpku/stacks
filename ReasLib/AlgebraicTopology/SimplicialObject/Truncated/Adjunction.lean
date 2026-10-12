/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.ColimitMap
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Adjunctions for truncated simplicial objects

This file packages skeleton, truncation, and coskeleton as an adjoint triple, constructs the
canonical skeleton-to-coskeleton comparison at the minimal extension boundary, and exposes the
adjointness of the coskeleton functor to typeclass search.  The target-pullback existence instance
is deliberately specialized to `Truncated.cosk`: the generic preservation theorem remains opt-in,
while downstream coskeleton comparison maps elaborate without local instance declarations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] (n : ℕ)
variable [SimplicialObject.Truncated.HasPointwiseSkeletons A n]

/-- The component of the inverse to the skeleton-adjunction unit, supplied by the singular
pointwise left-Kan-extension unit isomorphism. -/
/- no direct Stacks tag: generic skeleton/truncation adjunction support. -/
noncomputable def skAdj.unitInvApp (U : SimplicialObject.Truncated A n) :
    (SimplicialObject.Truncated.sk n ⋙
        SimplicialObject.truncation n).obj U ⟶ U :=
  (Functor.LeftKanExtension.unitIso
    (SimplexCategory.Truncated.inclusion n).op U).inv

/-- The inverse skeleton-unit components are natural in the truncated simplicial object. -/
theorem skAdj.unitInvApp.naturality {U V : SimplicialObject.Truncated A n}
    (f : U ⟶ V) :
    (SimplicialObject.Truncated.sk n ⋙ SimplicialObject.truncation n).map f ≫
        skAdj.unitInvApp n V =
      skAdj.unitInvApp n U ≫ f := sorry

/-- The inverse natural transformation to the skeleton-adjunction unit. -/
noncomputable def skAdj.unitInv :
    SimplicialObject.Truncated.sk n ⋙ SimplicialObject.truncation n ⟶
      𝟭 (SimplicialObject.Truncated A n) where
  app U := skAdj.unitInvApp n U
  naturality _ _ f := skAdj.unitInvApp.naturality n f

/-- The inverse skeleton-unit natural transformation has the expected pointwise component. -/
@[simp]
theorem skAdj.unitInv_app (U : SimplicialObject.Truncated A n) :
    (skAdj.unitInv (A := A) n).app U = skAdj.unitInvApp n U := sorry

/-- The skeleton-adjunction unit followed by its pointwise inverse is the identity. -/
theorem skAdj.unit_comp_unitInv :
    ((SimplexCategory.Truncated.inclusion n).op.lanAdjunction A).unit ≫
        skAdj.unitInv (A := A) n =
      𝟙 _ := sorry

/-- The pointwise inverse followed by the skeleton-adjunction unit is the identity. -/
theorem skAdj.unitInv_comp_unit :
    skAdj.unitInv (A := A) n ≫
        ((SimplexCategory.Truncated.inclusion n).op.lanAdjunction A).unit =
      𝟙 _ := sorry

/-- The unit of the skeleton/truncation adjunction as a natural isomorphism.  Its inverse is
assembled from the singular pointwise left-Kan-extension unit isomorphisms; neither the unit nor
its inverse requires a coskeleton hypothesis. -/
noncomputable def skAdj.unitIso :
    𝟭 (SimplicialObject.Truncated A n) ≅
      SimplicialObject.Truncated.sk n ⋙ SimplicialObject.truncation n where
  hom := ((SimplexCategory.Truncated.inclusion n).op.lanAdjunction A).unit
  inv := skAdj.unitInv n
  hom_inv_id := skAdj.unit_comp_unitInv n
  inv_hom_id := skAdj.unitInv_comp_unit n

/-- The inverse skeleton unit is computed by the pointwise left-Kan-extension unit isomorphism. -/
@[simp]
theorem skAdj.unitIso_inv_app (U : SimplicialObject.Truncated A n) :
    (skAdj.unitIso (A := A) n).inv.app U =
      (Functor.LeftKanExtension.unitIso
        (SimplexCategory.Truncated.inclusion n).op U).inv := sorry

variable [SimplicialObject.Truncated.HasCoskeletons A n]

/-- Skeleton, truncation, and coskeleton form the canonical adjoint triple
`sk n ⊣ truncation n ⊣ cosk n`. -/
noncomputable def adjointTriple :
    Adjunction.Triple (SimplicialObject.Truncated.sk (C := A) n)
      (SimplicialObject.truncation (C := A) n)
      (SimplicialObject.Truncated.cosk (C := A) n) :=
  ⟨SimplicialObject.skAdj n, SimplicialObject.coskAdj n⟩

/-- The canonical skeleton-to-coskeleton comparison.  This is Mathlib's adjoint-triple
`leftToRight` formula expressed with the explicit skeleton-unit isomorphism, which keeps the
minimal assumption of ordinary coskeleton existence. -/
noncomputable def skToCosk :
    SimplicialObject.Truncated.sk (C := A) n ⟶
      SimplicialObject.Truncated.cosk (C := A) n :=
  (SimplicialObject.Truncated.sk n).rightUnitor.inv ≫
    Functor.whiskerLeft (SimplicialObject.Truncated.sk n)
      (SimplicialObject.coskAdj n).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (skAdj.unitIso (A := A) n).inv
      (SimplicialObject.Truncated.cosk n) ≫
    (SimplicialObject.Truncated.cosk n).leftUnitor.hom

namespace skToCosk

/-- A component of the skeleton-to-coskeleton comparison is the mate of the inverse skeleton
unit under the coskeleton adjunction. -/
@[simp]
theorem app (U : SimplicialObject.Truncated A n) :
    (skToCosk (A := A) n).app U =
      ((SimplicialObject.coskAdj n).homEquiv
        ((SimplicialObject.Truncated.sk n).obj U) U)
        ((skAdj.unitIso (A := A) n).app U).inv := sorry

namespace homEquiv

/-- Transposing the comparison back across the coskeleton adjunction recovers the inverse
skeleton unit. -/
@[simp]
theorem symm_app (U : SimplicialObject.Truncated A n) :
    ((SimplicialObject.coskAdj n).homEquiv
        ((SimplicialObject.Truncated.sk n).obj U) U).symm
        ((skToCosk (A := A) n).app U) =
      (skAdj.unitIso (A := A) n).inv.app U := sorry

end homEquiv

/-- When both extensions are pointwise, the minimal-assumption comparison agrees with Mathlib's
canonical `Adjunction.Triple.leftToRight`. -/
theorem eq_leftToRight
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A n] :
    skToCosk (A := A) n =
      (adjointTriple (A := A) n).leftToRight := sorry

end skToCosk

end CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory.SimplicialObject.Truncated.cosk

variable {C : Type u} [Category.{v} C] {n : ℕ}
variable [SimplicialObject.Truncated.HasCoskeletons C n]

/-- The `n`-coskeleton functor is canonically a right adjoint to truncation. -/
@[stacks 018C "coskeleton is a right adjoint"]
noncomputable instance isRightAdjoint :
    (Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C).IsRightAdjoint :=
  sorry

/-- A pullback in truncated simplicial objects induces the corresponding pullback of its image
under the `n`-coskeleton functor. -/
@[stacks 018D "coskeleton preserves pullbacks"]
noncomputable instance hasPullback {U V W : SimplicialObject.Truncated C n}
    (f : U ⟶ V) (g : W ⟶ V) [HasPullback f g] :
    HasPullback ((Truncated.cosk n).map f) ((Truncated.cosk n).map g) :=
  sorry

end CategoryTheory.SimplicialObject.Truncated.cosk
