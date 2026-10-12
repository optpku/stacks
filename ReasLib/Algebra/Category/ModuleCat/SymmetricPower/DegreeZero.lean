/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower.Multiplication
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zeroth symmetric powers in `ModuleCat`

The empty symmetric tensor is canonically the tensor unit.  This file exposes the
projection, its inverse unit, and the corresponding natural isomorphism so that
presheaf and sheaf constructions do not need to unfold the quotient model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace ModuleCat.symmetricPower

variable {R : Type u} [CommRing R]

/-- The empty symmetric multilinear map is invariant under permutations. -/
theorem degreeZero_invariant (M : ModuleCat.{u} R) :
    SymmetricPower.IsInvariant
      (MultilinearMap.constOfIsEmpty R
        (fun _ : SymmetricPower.UFin 0 ↦ M) (1 : R)) := sorry

/-- The canonical projection from the zeroth symmetric power to the coefficient module. -/
@[stacks 01CF "zeroth symmetric power projection"]
noncomputable def degreeZero (M : ModuleCat.{u} R) :
    M.symmetricPower 0 ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom
    (SymmetricPower.lift
      (MultilinearMap.constOfIsEmpty R
        (fun _ : SymmetricPower.UFin 0 ↦ M) (1 : R))
      (degreeZero_invariant M))

/-- The zeroth symmetric-power projection evaluates to one on the empty generator. -/
@[simp]
theorem degreeZero_mk {M : ModuleCat.{u} R}
    (m : SymmetricPower.UFin 0 → M) :
    degreeZero M (ModuleCat.symmetricPower.mk m) = 1 := sorry

/-- The projection followed by the canonical symmetric unit is the identity. -/
theorem degreeZero_hom_inv_id (M : ModuleCat.{u} R) :
    degreeZero M ≫ ModuleCat.symmetricPower.one M = 𝟙 _ := sorry

/-- The canonical symmetric unit followed by the projection is the identity. -/
theorem degreeZero_inv_hom_id (M : ModuleCat.{u} R) :
    ModuleCat.symmetricPower.one M ≫ degreeZero M = 𝟙 _ := sorry

/-- The canonical zeroth symmetric-power isomorphism. -/
@[stacks 01CF "zeroth symmetric power isomorphism"]
noncomputable def iso₀ (M : ModuleCat.{u} R) :
    M.symmetricPower 0 ≅ ModuleCat.of R R :=
  { hom := degreeZero M
    inv := ModuleCat.symmetricPower.one M
    hom_inv_id := degreeZero_hom_inv_id M
    inv_hom_id := degreeZero_inv_hom_id M }

/-- The canonical zeroth symmetric-power isomorphism evaluates to one on the empty generator. -/
@[simp]
theorem iso₀_hom_apply {M : ModuleCat.{u} R}
    (m : SymmetricPower.UFin 0 → M) :
    (iso₀ M).hom (ModuleCat.symmetricPower.mk m) = 1 := sorry

/-- The inverse zeroth symmetric-power isomorphism is the canonical symmetric unit. -/
@[simp, stacks 01CF "inverse zeroth symmetric power evaluation"]
theorem iso₀_inv_apply (M : ModuleCat.{u} R) (r : R) :
    (iso₀ M).inv r = ModuleCat.symmetricPower.one M r := sorry

/-- The canonical zeroth symmetric-power isomorphism is natural in the module. -/
@[reassoc (attr := simp), stacks 01CF "zeroth symmetric power isomorphism naturality"]
theorem iso₀_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.symmetricPower.map f 0 ≫ (iso₀ N).hom =
      (iso₀ M).hom ≫ ((Functor.const _).obj (ModuleCat.of R R)).map f := sorry

/-- The inverse zeroth symmetric-power isomorphism is natural in the module. -/
@[stacks 01CF "inverse zeroth symmetric power isomorphism naturality"]
theorem iso₀_inv_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Functor.const _).obj (ModuleCat.of R R)).map f ≫ (iso₀ N).inv =
      (iso₀ M).inv ≫ ModuleCat.symmetricPower.map f 0 := sorry

/-- The zeroth symmetric-power projection is an isomorphism. -/
instance degreeZero_isIso (M : ModuleCat.{u} R) :
    IsIso (degreeZero M) := sorry

/-- The symmetric degree-zero unit is an isomorphism. -/
instance one_isIso (M : ModuleCat.{u} R) :
    IsIso (ModuleCat.symmetricPower.one M) := sorry

/-- Zeroth symmetric-power projections are natural in the module. -/
@[reassoc]
theorem degreeZero_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.symmetricPower.map f 0 ≫ degreeZero N = degreeZero M := sorry

/-- The degree-zero maps form the forward natural transformation to the tensor unit. -/
@[stacks 01CF "forward zeroth symmetric power natural transformation"]
noncomputable def degreeZeroNatTrans :
    ModuleCat.symmetricPower.functor R 0 ⟶
      (Functor.const _).obj (ModuleCat.of R R) where
  app M := (iso₀ M).hom
  naturality _ _ f := iso₀_hom_naturality f

/-- The inverse components of the degree-zero identifications form the reverse transformation. -/
@[stacks 01CF "inverse zeroth symmetric power natural transformation"]
noncomputable def degreeZeroInvNatTrans :
    (Functor.const _).obj (ModuleCat.of R R) ⟶ ModuleCat.symmetricPower.functor R 0 where
  app M := (iso₀ M).inv
  naturality _ _ f := iso₀_inv_naturality f

/-- The forward degree-zero natural transformation followed by its inverse is the identity. -/
@[simp]
theorem degreeZeroNatTrans_hom_inv_id :
    degreeZeroNatTrans (R := R) ≫ degreeZeroInvNatTrans (R := R) = 𝟙 _ := sorry

/-- The inverse degree-zero natural transformation followed by the forward one is the identity. -/
@[simp]
theorem degreeZeroNatTrans_inv_hom_id :
    degreeZeroInvNatTrans (R := R) ≫ degreeZeroNatTrans (R := R) = 𝟙 _ := sorry

/-- Zeroth symmetric powers are naturally the tensor-unit functor. -/
@[stacks 01CF "natural zeroth symmetric power"]
noncomputable def degreeZeroNatIso :
    ModuleCat.symmetricPower.functor R 0 ≅
      (Functor.const _).obj (ModuleCat.of R R) :=
  { hom := degreeZeroNatTrans (R := R)
    inv := degreeZeroInvNatTrans (R := R)
    hom_inv_id := degreeZeroNatTrans_hom_inv_id (R := R)
    inv_hom_id := degreeZeroNatTrans_inv_hom_id (R := R) }

/-- A component of `degreeZeroNatIso` is `iso₀`. -/
@[simp]
theorem degreeZeroNatIso_app (M : ModuleCat.{u} R) :
    (degreeZeroNatIso (R := R)).app M = iso₀ M := sorry

/-- The forward map of `degreeZeroNatIso` is explicit. -/
@[simp]
theorem degreeZeroNatIso_hom :
    (degreeZeroNatIso (R := R)).hom = degreeZeroNatTrans (R := R) := sorry

/-- The inverse map of `degreeZeroNatIso` is explicit. -/
@[simp]
theorem degreeZeroNatIso_inv :
    (degreeZeroNatIso (R := R)).inv = degreeZeroInvNatTrans (R := R) := sorry

/-- The forward component of `degreeZeroNatIso` is `degreeZero`. -/
@[simp]
theorem degreeZeroNatIso_hom_app (M : ModuleCat.{u} R) :
    (degreeZeroNatIso (R := R)).hom.app M = degreeZero M := sorry

/-- The inverse component of `degreeZeroNatIso` is the symmetric unit. -/
@[simp]
theorem degreeZeroNatIso_inv_app (M : ModuleCat.{u} R) :
    (degreeZeroNatIso (R := R)).inv.app M = (iso₀ M).inv := sorry

end ModuleCat.symmetricPower
