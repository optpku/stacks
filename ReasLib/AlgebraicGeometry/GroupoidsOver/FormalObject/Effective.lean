/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Approximation

/-!
# Effective formal objects

A formal object of a category fibred in groupoids over `(Sch/S)_fppf` is
effective when it lies in the essential image of the approximation functor
from complete local objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
  {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, v} (Over S)}

/-- A formal object is effective if it lies in the essential image of the
approximation functor from objects over complete local finite-type-residue
spectra. -/
class IsEffective (ξ : FormalObject X) : Prop where
  /-- The formal object is isomorphic to the approximation of some complete
  local object. -/
  mem_essImage : (GroupoidsOver.approximation X).essImage ξ

/-- The approximation of an object over a complete local spectrum is effective. -/
instance instIsEffective_obj (x : CompleteLocalObject X) :
    IsEffective ((GroupoidsOver.approximation X).obj x) where
  mem_essImage := Functor.obj_mem_essImage (GroupoidsOver.approximation X) x

/-- Effectiveness is membership in the essential image of approximation. -/
theorem isEffective_iff {ξ : FormalObject X} :
    IsEffective ξ ↔ (GroupoidsOver.approximation X).essImage ξ :=
  ⟨fun h ↦ h.mem_essImage, fun h ↦ ⟨h⟩⟩

/-- A formal object is effective if and only if it is isomorphic to the
approximation of some complete local object. -/
theorem isEffective_iff_exists {ξ : FormalObject X} :
    IsEffective ξ ↔
      ∃ x : CompleteLocalObject X,
        Nonempty ((GroupoidsOver.approximation X).obj x ≅ ξ) :=
  isEffective_iff

/-- The successor comparison factors the cartesian restriction at stage `n`. -/
theorem restrictionHom_fac (x : CompleteLocalObject X) (n : ℕ) :
    restrictionStep x n ≫ restrictionHom x (n + 1) = restrictionHom x n :=
  @Functor.IsStronglyCartesian.fac _ _ _ _ X.p _ _ _ _
    (x.base.truncationOverHom (n + 1)) (restrictionHom x (n + 1))
    (restrictionHom_isStronglyCartesian x (n + 1)) _ _ _ _
    (x.base.truncationOverHom_comp n) (restrictionHom x n)
    (restrictionHom_isCartesian x n).toIsHomLift

/-- Algebraization over the stored complete local base, with fibre isomorphisms
compatible with every successor map. This retains the specified base and is
stronger data than membership in the essential image alone. -/
def IsEffectiveOverBase (ξ : FormalObject X) : Prop :=
  ∃ (x : X.total) (hx : X.p.obj x = Over.mk ξ.base.toS)
    (α : ∀ n, restrictionObj (CompleteLocalObject.of ξ.base x hx) n ≅ ξ.objects n),
    (∀ n, X.p.IsHomLift (𝟙 (ξ.base.stageOver n)) (α n).hom) ∧
      ∀ n, restrictionStep (CompleteLocalObject.of ξ.base x hx) n ≫
        (α (n + 1)).hom = (α n).hom ≫ ξ.step n

/-- A compatible algebraization over the specified base gives an effective
formal object in the usual essential-image sense. -/
theorem IsEffectiveOverBase.isEffective {ξ : FormalObject X}
    (h : IsEffectiveOverBase ξ) : IsEffective ξ := by
  obtain ⟨x, hx, α, _, hα⟩ := h
  let a : Hom (restriction (CompleteLocalObject.of ξ.base x hx)) ξ :=
    Hom.ofStages (fun n ↦ (α n).hom) hα
  let e : (restriction (CompleteLocalObject.of ξ.base x hx)).toFunctor ≅ ξ.toFunctor :=
    NatIso.ofComponents α (fun f ↦ a.naturality f)
  exact ⟨⟨CompleteLocalObject.of ξ.base x hx,
    ⟨{ hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id,
       inv_hom_id := e.inv_hom_id }⟩⟩⟩

end AlgebraicGeometry.GroupoidsOver.FormalObject
