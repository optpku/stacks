/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.Total
import Mathlib.Tactic.CrossRefAttribute

/-!
# Decomposition of exterior algebras

The exterior algebra of a module is the coproduct of its homogeneous exterior powers. The
isomorphism in this file is explicit: it combines Mathlib's graded-algebra decomposition with
the identification of direct sums and categorical coproducts in `ModuleCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

noncomputable section

universe u v

namespace ModuleCat

variable {R : Type u} [CommRing R]

namespace exteriorAlgebra

/-- The inclusion of the degree-`n` homogeneous exterior power into the exterior algebra. -/
@[stacks 01CF "homogeneous inclusion into an exterior algebra"]
noncomputable def powerι (M : ModuleCat.{v} R) (n : ℕ) :
    M.exteriorPower n ⟶ M.exteriorAlgebra :=
  ModuleCat.ofHom (⋀[R]^n M).subtype

/-- The graded-algebra decomposition with its concrete direct-sum target. -/
@[stacks 01CF "exterior algebra as a direct sum of exterior powers"]
noncomputable def directSumIso (M : ModuleCat.{v} R) :
    M.exteriorAlgebra ≅ ModuleCat.of R (⨁ n : ℕ, M.exteriorPower n) :=
  (DirectSum.decomposeAlgEquiv
    (fun n : ℕ ↦ ⋀[R]^n M)).toLinearEquiv.toModuleIso

/-- The exterior algebra is the categorical coproduct of its exterior powers. -/
@[stacks 01CF "exterior algebra as the coproduct of exterior powers"]
noncomputable def decompositionIso (M : ModuleCat.{v} R) :
    M.exteriorAlgebra ≅ ∐ fun n : ℕ ↦ M.exteriorPower n :=
  directSumIso M ≪≫
    (ModuleCat.coprodIsoDirectSum
      (fun n : ℕ ↦ M.exteriorPower n)).symm

/-- The forward concrete decomposition is `DirectSum.decompose`. -/
@[simp]
theorem directSumIso_hom_apply (M : ModuleCat.{v} R)
    (x : M.exteriorAlgebra) :
    (directSumIso M).hom x =
      DirectSum.decompose (fun n : ℕ ↦ ⋀[R]^n M) x := sorry

/-- A homogeneous exterior power maps to its coproduct summand. -/
@[reassoc (attr := simp)]
theorem powerι_decompositionIso_hom (M : ModuleCat.{v} R) (n : ℕ) :
    powerι M n ≫ (decompositionIso M).hom =
      Limits.Sigma.ι (fun n : ℕ ↦ M.exteriorPower n) n := sorry

/-- The inverse decomposition restricts on each summand to the homogeneous inclusion. -/
@[reassoc (attr := simp)]
theorem ι_decompositionIso_inv (M : ModuleCat.{v} R) (n : ℕ) :
    Limits.Sigma.ι (fun n : ℕ ↦ M.exteriorPower n) n ≫
        (decompositionIso M).inv =
      powerι M n := sorry

/-- Exterior-power maps commute with their homogeneous inclusions into exterior algebras. -/
@[reassoc]
theorem map_powerι {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) :
    exteriorPower.map f n ≫ powerι N n =
      powerι M n ≫ map f := sorry

/-- For fixed degree, homogeneous inclusion is natural in the module. -/
@[stacks 01CF "natural homogeneous inclusion into an exterior algebra"]
noncomputable def powerιNatTrans (n : ℕ) :
    (exteriorPower.functor R n :
      ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R) ⟶
      exteriorAlgebra.functor R where
  app M := powerι M n
  naturality _ _ f := map_powerι f n

/-- A component of the fixed-degree homogeneous inclusion is `powerι`. -/
@[simp]
theorem powerιNatTrans_app (M : ModuleCat.{max u v} R) (n : ℕ) :
    (powerιNatTrans (R := R) n).app M = powerι M n := sorry

/-- The degree-one exterior-power inclusion is the usual exterior-algebra generator. -/
@[reassoc (attr := simp)]
theorem degreeOne_powerι (M : ModuleCat.{max u v} R) :
    exteriorPower.degreeOne M ≫ powerι M 1 = ιHom M := sorry

/-- Under the total decomposition, the usual generator lands in the degree-one summand. -/
@[reassoc (attr := simp)]
theorem ιHom_decompositionIso_hom (M : ModuleCat.{max u v} R) :
    ιHom M ≫ (decompositionIso M).hom =
      exteriorPower.degreeOne M ≫
        Limits.Sigma.ι (fun n : ℕ ↦ M.exteriorPower n) 1 := sorry

/-- The exterior-algebra decomposition is natural in the module. -/
@[stacks 01CF "exterior-algebra decomposition forward naturality"]
theorem map_decompositionIso_hom {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    map f ≫ (decompositionIso N).hom =
      (decompositionIso M).hom ≫
        (exteriorPower.totalFunctor (R := R)).map f := sorry

/-- The inverse exterior-algebra decomposition is natural in the module. -/
@[stacks 01CF "exterior-algebra decomposition inverse naturality"]
theorem decompositionIso_inv_naturality
    {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (exteriorPower.totalFunctor (R := R)).map f ≫
        (decompositionIso N).inv =
      (decompositionIso M).inv ≫ map f := sorry

/-- The forward exterior-algebra decompositions form a natural transformation to the total
exterior-power functor. -/
@[stacks 01CF "exterior-algebra decomposition natural transformation"]
noncomputable def decompositionNatTrans :
    exteriorAlgebra.functor R ⟶ exteriorPower.totalFunctor (R := R) where
  app M := (decompositionIso M).hom
  naturality _ _ f := map_decompositionIso_hom f

/-- The inverse exterior-algebra decompositions form a natural transformation from the total
exterior-power functor. -/
@[stacks 01CF "inverse exterior-algebra decomposition natural transformation"]
noncomputable def decompositionInvNatTrans :
    exteriorPower.totalFunctor (R := R) ⟶ exteriorAlgebra.functor R where
  app M := (decompositionIso M).inv
  naturality _ _ f := decompositionIso_inv_naturality f

/-- A component of the forward decomposition natural transformation is the forward objectwise
decomposition. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural transformation component"]
theorem decompositionNatTrans_app (M : ModuleCat.{v} R) :
    (decompositionNatTrans (R := R)).app M = (decompositionIso M).hom := sorry

/-- A component of the inverse decomposition natural transformation is the inverse objectwise
decomposition. -/
@[simp, stacks 01CF "inverse exterior-algebra decomposition natural transformation component"]
theorem decompositionInvNatTrans_app (M : ModuleCat.{v} R) :
    (decompositionInvNatTrans (R := R)).app M = (decompositionIso M).inv := sorry

/-- The forward exterior-algebra decomposition transformation followed by its inverse is the
identity. -/
@[simp, stacks 01CF "exterior-algebra decomposition forward-inverse law"]
theorem decompositionNatTrans_hom_inv_id :
    decompositionNatTrans (R := R) ≫ decompositionInvNatTrans (R := R) = 𝟙 _ := sorry

/-- The inverse exterior-algebra decomposition transformation followed by the forward one is
the identity. -/
@[simp, stacks 01CF "exterior-algebra decomposition inverse-forward law"]
theorem decompositionNatTrans_inv_hom_id :
    decompositionInvNatTrans (R := R) ≫ decompositionNatTrans (R := R) = 𝟙 _ := sorry

/-- Exterior algebras are naturally the total functor of exterior powers. -/
@[stacks 01CF "natural exterior-algebra decomposition"]
noncomputable def decompositionNatIso :
    exteriorAlgebra.functor R ≅ exteriorPower.totalFunctor (R := R) where
  hom := decompositionNatTrans (R := R)
  inv := decompositionInvNatTrans (R := R)
  hom_inv_id := decompositionNatTrans_hom_inv_id (R := R)
  inv_hom_id := decompositionNatTrans_inv_hom_id (R := R)

/-- A component of `decompositionNatIso` is the objectwise exterior-algebra decomposition. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism component"]
theorem decompositionNatIso_app (M : ModuleCat.{v} R) :
    (decompositionNatIso (R := R)).app M = decompositionIso M := sorry

/-- The forward transformation of `decompositionNatIso` is the explicit decomposition
transformation. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism hom"]
theorem decompositionNatIso_hom :
    (decompositionNatIso (R := R)).hom = decompositionNatTrans (R := R) := sorry

/-- The inverse transformation of `decompositionNatIso` is the explicit inverse decomposition
transformation. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism inverse"]
theorem decompositionNatIso_inv :
    (decompositionNatIso (R := R)).inv = decompositionInvNatTrans (R := R) := sorry

/-- The forward component of `decompositionNatIso` is the forward objectwise decomposition. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism hom component"]
theorem decompositionNatIso_hom_app (M : ModuleCat.{v} R) :
    (decompositionNatIso (R := R)).hom.app M = (decompositionIso M).hom := sorry

/-- The inverse component of `decompositionNatIso` is the inverse objectwise decomposition. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism inverse component"]
theorem decompositionNatIso_inv_app (M : ModuleCat.{v} R) :
    (decompositionNatIso (R := R)).inv.app M = (decompositionIso M).inv := sorry

end exteriorAlgebra

end ModuleCat
