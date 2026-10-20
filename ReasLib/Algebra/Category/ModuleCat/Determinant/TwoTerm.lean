/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Determinant.ExteriorPower
public import ReasLib.Algebra.Homology.CochainComplex.Determinant.CanonicalElement
public import ReasLib.Algebra.Homology.CochainComplex.TwoTerm

@[expose] public section

open CategoryTheory
open scoped Module.Determinant

noncomputable section

universe u v

namespace CochainComplex.Determinant

variable {R : Type u} [CommRing R]
variable {N M : ModuleCat.{v} R}

/-- Equal finite-free endpoint ranks make the associated two-term cochain complex rank zero. -/
theorem IsRankZero.twoTerm_of_finrank_eq (d : N ⟶ M)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R N = Module.finrank R M) :
    IsRankZero (CochainComplex.twoTerm d) := sorry

end CochainComplex.Determinant

namespace ModuleCat

variable {R : Type u} [CommRing R]
variable {N M : ModuleCat.{v} R}

/-- The discriminant element of a two-term finite-free complex `N ⟶ M`, represented as a
linear map from `det(N)` to `det(M)`. -/
noncomputable def twoTermDiscriminant (d : N ⟶ M)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R N = Module.finrank R M) :
    det[R](N) →ₗ[R] det[R](M) :=
  (Module.Determinant.mapIso
      (CochainComplex.twoTermXZeroIso d).toLinearEquiv).toLinearMap.comp
    ((CochainComplex.Determinant.canonical (CochainComplex.twoTerm d)
      (CochainComplex.Determinant.IsRankZero.twoTerm_of_finrank_eq d hRank)).comp
        (Module.Determinant.mapIso
          (CochainComplex.twoTermXNegOneIso d).symm.toLinearEquiv).toLinearMap)

/-- Evaluation of the two-term discriminant is induced by the differential on exterior
algebras. -/
theorem twoTermDiscriminant_apply (d : N ⟶ M)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R N = Module.finrank R M)
    (z : det[R](N)) :
    ((twoTermDiscriminant d hRank z : det[R](M)) : ExteriorAlgebra R M) =
      ExteriorAlgebra.map d.hom (z : ExteriorAlgebra R N) := sorry

/-- The two-term discriminant is the determinant-line map induced by the map on top exterior
powers. -/
theorem twoTermDiscriminant_eq_mapTopExteriorPower (d : N ⟶ M)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R M] [Module.Finite R M]
    (hRank : Module.finrank R N = Module.finrank R M) :
    twoTermDiscriminant d hRank =
      Determinant.mapTopExteriorPower N M (Module.finrank R N) rfl hRank.symm
        (ModuleCat.exteriorPower.map d (Module.finrank R N)).hom := sorry

end ModuleCat

end
