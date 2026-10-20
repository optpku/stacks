/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange
public import Mathlib.Algebra.Algebra.Basic

/-!
# Canonical residue change

The residue change of the residue object of a finite field extension is canonically
identified with the residue object of the base field.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ArtinianLocalAlgCat

universe u

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]

namespace ArtinianLocalAlgCat



/-- The inverse algebra map of `residueChangeResidueIso`, sending `x : k` to the matching
pair `(algebraMap k l x, x)` in `l ×_l k`. -/
def residueChangeResidueIsoInvHom :
    (residue Λ k).carrier →ₐ[Λ] (residueChange k (residue Λ l)).carrier := by
  let f := (IsScalarTower.toAlgHom Λ k l).prod (AlgHom.id Λ k)
  have laws : ∀ x : k, f x ∈
      AlgHom.pullback (toResidue (residue Λ l)).hom (IsScalarTower.toAlgHom Λ k l) := by
    sorry
  exact AlgHom.codRestrict f _ laws

/-- The identification `l ×_l k ≅ k` in `C_{Λ, k}`, comparing residue change of the residue
object `l` with the residue object `k`. -/
def residueChangeResidueIso :
    residueChange k (residue Λ l) ≅ residue Λ k := by
  let f := residueChangeResidueIsoInvHom Λ k l
  let g := residueChangeSnd k (residue Λ l)
  have laws : IsLocalHom f ∧
      (∀ h : IsLocalHom f, residueCompat f h = residueIsoHom (residue Λ k)) ∧
      (∀ (h : IsLocalHom f) (hc : residueCompat f h = residueIsoHom (residue Λ k)),
        g ≫ Hom.of f h hc = 𝟙 (residueChange k (residue Λ l))) ∧
      (∀ (h : IsLocalHom f) (hc : residueCompat f h = residueIsoHom (residue Λ k)),
        Hom.of f h hc ≫ g = 𝟙 (residue Λ k)) := by
    sorry
  exact
    { hom := g
      inv := Hom.of f laws.1 (laws.2.1 laws.1)
      hom_inv_id := laws.2.2.1 laws.1 (laws.2.1 laws.1)
      inv_hom_id := laws.2.2.2 laws.1 (laws.2.1 laws.1) }

/-- The inverse morphism of `residueChangeResidueIso` is `residueChangeResidueIsoInvHom`. -/
theorem residueChangeResidueIso_inv :
    (residueChangeResidueIso Λ k l).inv.hom = residueChangeResidueIsoInvHom Λ k l :=
  rfl

end ArtinianLocalAlgCat
