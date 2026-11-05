/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Affine
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective

/-!
# Formal systems of families of curves

Formal systems over complete local algebras are effective when they arise
from a family of curves with compatible isomorphisms on all truncations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Functor
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

local instance : IsLocallyNoetherian specZ.{u} := by
  letI : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  infer_instance

/-- An Artin formal object of Curves over `specZ`: a complete local
`specZ`-algebra together with a compatible system of families of curves over
the truncations `Spec(R ⧸ m^{n+1})`. -/
abbrev FormalObject := GroupoidsOver.FormalObject (toGroupoids specZ)

namespace FormalObject

/-- The complete local base, inherited from the public formal object. -/
abbrev base (ξ : FormalObject) := GroupoidsOver.FormalObject.base ξ

/-- The stages, inherited from the public formal object. -/
abbrev objects (ξ : FormalObject) := GroupoidsOver.FormalObject.objects ξ

/-- The successor maps, inherited from the public formal object. -/
abbrev step (ξ : FormalObject) := GroupoidsOver.FormalObject.step ξ

/-- The stage projections, inherited from the public formal object. -/
abbrev over_obj (ξ : FormalObject) := GroupoidsOver.FormalObject.over_obj ξ

/-- The transition projections, inherited from the public formal object. -/
abbrev over_step (ξ : FormalObject) := GroupoidsOver.FormalObject.over_step ξ

/-- Package a complete local `specZ`-algebra and a compatible forward system as
a formal object of Curves. -/
def of (base : CompleteLocalSAlgebra specZ) (objects : ℕ → Obj specZ)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, (p specZ).obj (objects n) = base.stageOver n)
    (over_step : ∀ n, (p specZ).IsHomLift (base.stageHom n) (step n)) :
    FormalObject :=
  GroupoidsOver.FormalObject.of base objects step over_obj over_step

/-- Compatibility constructor for the former curve-specific structure. -/
abbrev mk := of

/-- The packaged formal object recovers the supplied complete local
`specZ`-algebra. -/
theorem of_base (base : CompleteLocalSAlgebra specZ) (objects : ℕ → Obj specZ)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, (p specZ).obj (objects n) = base.stageOver n)
    (over_step : ∀ n, (p specZ).IsHomLift (base.stageHom n) (step n)) :
    (of base objects step over_obj over_step).base = base := rfl

/-- Stagewise specification of a formal object over the truncations of its
base. -/
theorem spec (ξ : FormalObject) (n : ℕ) :
    (p specZ).obj (ξ.objects n) = ξ.base.stageOver n ∧
      (p specZ).IsHomLift (ξ.base.stageHom n) (ξ.step n) :=
  ⟨ξ.over_obj n, ξ.over_step n⟩

/-- Restriction of a family of curves along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionObj {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) : Obj specZ :=
  GroupoidsOver.FormalObject.restrictionObj
    (GroupoidsOver.CompleteLocalObject.of (X := toGroupoids specZ) R x hx) n

/-- Cartesian lift of restriction along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionHom {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    restrictionObj x hx n ⟶ x :=
  GroupoidsOver.FormalObject.restrictionHom
    (GroupoidsOver.CompleteLocalObject.of (X := toGroupoids specZ) R x hx) n

/-- Restriction of `x` to stage `n` is cartesian over `truncationOverHom`. -/
theorem restrictionHom_isCartesian {R : CompleteLocalSAlgebra specZ}
    (x : Obj specZ) (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    (p specZ).IsCartesian (R.truncationOverHom n) (restrictionHom x hx n) :=
  GroupoidsOver.FormalObject.restrictionHom_isCartesian
    (GroupoidsOver.CompleteLocalObject.of (X := toGroupoids specZ) R x hx) n

/-- Restriction of `x` to stage `n` is strongly cartesian. -/
theorem restrictionHom_isStronglyCartesian {R : CompleteLocalSAlgebra specZ}
    (x : Obj specZ) (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    (p specZ).IsStronglyCartesian (R.truncationOverHom n)
      (restrictionHom x hx n) :=
  GroupoidsOver.FormalObject.restrictionHom_isStronglyCartesian
    (GroupoidsOver.CompleteLocalObject.of (X := toGroupoids specZ) R x hx) n

/-- Stage `n` of the restricted system lies over `Spec(R ⧸ m^{n+1})`. -/
theorem restrictionObj_over {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    (p specZ).obj (restrictionObj x hx n) = R.stageOver n :=
  GroupoidsOver.FormalObject.restrictionObj_over
    (GroupoidsOver.CompleteLocalObject.of (X := toGroupoids specZ) R x hx) n

/-- Successor map of restrictions, obtained from transitivity of pullback along
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2}) ⟶ Spec(R)`. -/
def restrictionStep {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    restrictionObj x hx n ⟶ restrictionObj x hx (n + 1) :=
  GroupoidsOver.FormalObject.restrictionStep
    (GroupoidsOver.CompleteLocalObject.of (X := toGroupoids specZ) R x hx) n

/-- Successor maps of restrictions lift the truncated thickenings. -/
theorem restrictionStep_isHomLift {R : CompleteLocalSAlgebra specZ}
    (x : Obj specZ) (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    (p specZ).IsHomLift (R.stageHom n) (restrictionStep x hx n) :=
  GroupoidsOver.FormalObject.restrictionStep_isHomLift
    (GroupoidsOver.CompleteLocalObject.of (X := toGroupoids specZ) R x hx) n

/-- The successor comparison factors the cartesian restriction of stage `n`. -/
theorem restrictionHom_fac {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    restrictionStep x hx n ≫ restrictionHom x hx (n + 1) =
      restrictionHom x hx n :=
  GroupoidsOver.FormalObject.restrictionHom_fac
    (GroupoidsOver.CompleteLocalObject.of (X := toGroupoids specZ) R x hx) n

/-- A formal object of Curves over `specZ` is effective if it arises by
restriction from some family of curves over `Spec(R)`, with the restrictions
forming a transition-compatible system of fibre isomorphisms. -/
abbrev IsEffective (ξ : FormalObject) : Prop :=
  GroupoidsOver.FormalObject.IsEffectiveOverBase ξ

/-- Effectiveness is existence of an algebraization whose restrictions recover
the stages by a transition-compatible system of fibre isomorphisms. -/
theorem isEffective_iff (ξ : FormalObject) :
    IsEffective ξ ↔
      ∃ (x : Obj specZ) (hx : (p specZ).obj x = Over.mk ξ.base.toS)
        (α : ∀ n, restrictionObj x hx n ≅ ξ.objects n),
        (∀ n, (p specZ).IsHomLift (𝟙 (ξ.base.stageOver n)) (α n).hom) ∧
          ∀ n, restrictionStep x hx n ≫ (α (n + 1)).hom =
            (α n).hom ≫ ξ.step n := Iff.rfl

end FormalObject

/-- Every formal object of the stack of curves over `specZ` is effective. -/
theorem formalObject_isEffective (ξ : FormalObject) :
    FormalObject.IsEffective ξ := sorry

/-- The geometric algebraization theorem also gives effectiveness in the public
essential-image interface. -/
theorem formalObject_isEffective_public (ξ : FormalObject) :
    GroupoidsOver.FormalObject.IsEffective ξ :=
  GroupoidsOver.FormalObject.IsEffectiveOverBase.isEffective (formalObject_isEffective ξ)

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
