module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Cohomology
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of a selected derived internal Hom

This leaf transports the canonical module `RHom` cohomology comparison across an explicit
`RHom.ClosedComparison`.  The compatibility gate stays visible: a bare closed structure does not
identify its internal Hom with the canonical derived enriched Hom.

The pointwise comparison is natural in the target variable for each fixed source.  Source-variable
naturality requires an honest `RHom.BifunctorComparison` and is exposed by
`RHom.BifunctorComparison.Cohomology`, not by this leaf.

@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u g

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.Cohomology.Closed

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
variable [RHom.Has (A := A)]
variable [IsGrothendieckAbelian.{g} (ModuleCat.{u} A)]

/-- 0E1U: Cohomology of the internal Hom selected by a closed comparison is canonically shifted
derived Hom. -/
@[stacks 0E1U "selected internal-Hom cohomology linear equivalence"]
noncomputable def linearEquiv
    (M : RHom.ClosedComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        (InternalHom.obj M.closed K L) ≃ₗ[A] ShiftedHom K L n :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
      (RHom.ClosedComparison.objIso M K L)).symm.toLinearEquiv.trans
    (RHom.Cohomology.linearEquiv K L n)

/-- 0E1U: The selected comparison is canonical transport followed by the canonical `RHom`
cohomology equivalence. -/
@[simp, stacks 0E1U "selected internal-Hom cohomology evaluation"]
theorem linearEquiv_apply
    (M : RHom.ClosedComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (InternalHom.obj M.closed K L)) :
    linearEquiv M K L n x =
      RHom.Cohomology.linearEquiv K L n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
          (RHom.ClosedComparison.objIso M K L)).inv x) := rfl

/-- The selected-H cohomology equivalence carries target maps to shifted-Hom composition. -/
@[simp, stacks 0E1U "selected internal-Hom cohomology target naturality"]
theorem linearEquiv_natural_target
    (M : RHom.ClosedComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (InternalHom.obj M.closed K L₁)) :
    linearEquiv M K L₂ n
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          ((MonoidalClosed.ihomOf M.closed K).map f)).hom x) =
      linearEquiv M K L₁ n x ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).map f := by
  have hnat :
      (MonoidalClosed.ihomOf M.closed K).map f ≫ (M.objIso K L₂).inv =
        (M.objIso K L₁).inv ≫ RHom.map (A := A) (𝟙 K) f := by
    have h := (M.targetIso K).inv.naturality f
    change
      (MonoidalClosed.ihomOf M.closed K).map f ≫ (M.objIso K L₂).inv =
        (M.objIso K L₁).inv ≫ RHom.map (A := A) (𝟙 K) f at h
    exact h
  have hx :
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        (M.objIso K L₂).inv).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
            ((MonoidalClosed.ihomOf M.closed K).map f)).hom x) =
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
          (RHom.map (A := A) (𝟙 K) f)).hom
            (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
              (M.objIso K L₁).inv).hom x) := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp, hnat]
  rw [linearEquiv_apply, linearEquiv_apply]
  simp only [Functor.mapIso_inv]
  rw [hx, RHom.Cohomology.linearEquiv_natural_target]

/-- 0E1U: Degree-zero cohomology of a selected derived internal Hom is the ordinary derived
morphism module. -/
@[stacks 0E1U "selected internal-Hom degree-zero cohomology"]
noncomputable def linearEquiv_zero
    (M : RHom.ClosedComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (InternalHom.obj M.closed K L) ≃ₗ[A] (K ⟶ L) :=
  (linearEquiv M K L 0).trans (ShiftedHom.zeroLinearEquiv A K L)

/-- 0E1U: Evaluation of the selected degree-zero cohomology equivalence. -/
@[simp, stacks 0E1U "selected internal-Hom degree-zero cohomology evaluation"]
theorem linearEquiv_zero_apply
    (M : RHom.ClosedComparison (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (InternalHom.obj M.closed K L)) :
    linearEquiv_zero M K L x =
      ShiftedHom.zeroLinearEquiv A K L (linearEquiv M K L 0 x) := rfl

/-- The selected-H degree-zero equivalence carries target maps to composition. -/
@[simp, stacks 0E1U "selected internal-Hom degree-zero target naturality"]
theorem linearEquiv_zero_natural_target
    (M : RHom.ClosedComparison (A := A))
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (InternalHom.obj M.closed K L₁)) :
    linearEquiv_zero M K L₂
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((MonoidalClosed.ihomOf M.closed K).map f)).hom x) =
      linearEquiv_zero M K L₁ x ≫ f := by
  rw [linearEquiv_zero_apply, linearEquiv_zero_apply,
    linearEquiv_natural_target]
  generalize linearEquiv M K L₁ 0 x = g
  change
    (g ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) 0).map f) ≫
        (shiftFunctorZero' (DerivedCategory (ModuleCat.{u} A)) 0 rfl).hom.app L₂ =
      (g ≫ (shiftFunctorZero' (DerivedCategory (ModuleCat.{u} A)) 0 rfl).hom.app L₁) ≫ f
  rw [Category.assoc,
    (shiftFunctorZero' (DerivedCategory (ModuleCat.{u} A)) 0 rfl).hom.naturality f,
    ← Category.assoc]
  rw [Functor.id_map]
  rfl

end CategoryTheory.DerivedCategory.InternalHom.RHom.Cohomology.Closed
