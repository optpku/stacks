/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Cohomology
public import Mathlib.RepresentationTheory.Invariants

/-!
# Degree-zero continuous cohomology

Evaluation at the unit identifies degree-zero continuous cohomology with invariant vectors.
-/

@[expose] public section

noncomputable section

open CategoryTheory Abelian

universe u

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

variable {R G : Type u} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Continuous cohomology in degree zero is linearly equivalent to the invariant submodule
of the coefficient representation, by evaluation at the unit of the trivial coefficient. -/
def h0EquivInvariants (M : DiscreteModuleCat R G) :
    cohomologyObject R G 0 M ≃ₗ[R]
      ((Rep.ActionToRep R G).obj M.obj).ρ.invariants :=
  (Ext.linearEquiv₀ (R := R)).trans
    {
      toFun f := ⟨f.hom.hom.hom (1 : R), fun g ↦ by
        have h := congrArg (fun a ↦ a.hom (1 : R)) (f.hom.comm g)
        exact h.symm⟩
      invFun v := ObjectProperty.homMk
        { hom := ModuleCat.ofHom
            { toFun := fun a ↦ a • v.val
              map_add' := fun a b ↦ add_smul a b v.val
              map_smul' := fun a b ↦ mul_smul a b v.val }
          comm := fun g ↦ by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro a
            change R at a
            change a • v.val = (M.obj.ρ g).hom (a • v.val)
            exact (((Rep.ActionToRep R G).obj M.obj).ρ g).map_smul a v.val |>.trans
              (congrArg (fun w ↦ a • w) (v.property g)) |>.symm }
      left_inv f := by
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change R at a
        change a • f.hom.hom.hom (1 : R) = f.hom.hom.hom a
        let l : R →ₗ[R] M.obj.V := f.hom.hom.hom
        exact (l.map_smul a (1 : R)).symm.trans (congrArg l (mul_one a))
      right_inv v := by
        apply Subtype.ext
        exact one_smul R v.val
      map_add' f g := by
        apply Subtype.ext
        rfl
      map_smul' a f := by
        apply Subtype.ext
        rfl }

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
