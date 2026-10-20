module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank
public import ReasLib.LinearAlgebra.Dimension.FractionRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic Rank over a Domain

Over a domain, `Module.finrank` is the generic rank: equivalently, it is the
dimension after base change to the fraction field. The construction only needs
a commutative domain; PID structure is reserved for the inverse and
equivalence API in `Rank.PID`.

@stack 0FJ8
-/

@[expose] public section

noncomputable section

open CategoryTheory
universe u v

namespace CategoryTheory.ModuleCat.K0.Finite

variable (R : Type u) [CommRing R] [IsDomain R]

/-- Generic rank kills the short-exact relations defining the finite-module
Grothendieck group. The generator functional is ordinary `Module.finrank`. -/
@[stacks 0FJ8 "generic rank kills finite-module Grothendieck relations"]
theorem genericRank_relations :
    ObjectProperty.GrothendieckGroup.relations (ModuleCat.isFG.{v} R) ≤
      (FreeAbelianGroup.lift fun M : FGModuleCat.{v} R ↦
        (Module.finrank R M.obj : ℤ)).ker := sorry

/-- Generic rank as an additive map `K'_0(R) →+ ℤ` for a commutative domain. -/
@[stacks 0FJ8 "generic rank on finite-module K0"]
def genericRank : finite.{u, v} R →+ ℤ :=
  ObjectProperty.GrothendieckGroup.lift
    (fun M : FGModuleCat.{v} R ↦
      (Module.finrank R M.obj : ℤ))
    (genericRank_relations.{u, v} R)

/-- Generic rank evaluates on a bundled finite-module class by `Module.finrank`. -/
@[simp, stacks 0FJ8 "generic rank on finite-module generators"]
theorem genericRank_of (M : FGModuleCat.{v} R) :
    genericRank.{u, v} R (finiteOf R M) =
      (Module.finrank R M.obj : ℤ) := sorry

/-- Generic rank sends a virtual free finite-module class to its integer
coefficient. This direction needs only the domain hypothesis. -/
@[simp, stacks 0FJ8 "generic rank of virtual free classes"]
theorem genericRank_free (n : ℤ) :
    genericRank.{u, u} R (free R n) = n := sorry

end CategoryTheory.ModuleCat.K0.Finite

namespace CategoryTheory.ModuleCat.K0.Projective

variable (R : Type u) [CommRing R] [IsDomain R]

/-- Projective generic rank is finite generic rank after the canonical map
`K₀(R) →+ K'_0(R)`. -/
@[stacks 0FJ8 "generic rank on projective K0"]
def genericRank : projective.{u, v} R →+ ℤ :=
  (CategoryTheory.ModuleCat.K0.Finite.genericRank.{u, v} R).comp
    (projectiveToFinite.{u, v} R)

/-- Projective generic rank evaluates on a finite-projective generator by `Module.finrank`. -/
@[simp, stacks 0FJ8 "projective generic rank on generators"]
theorem genericRank_of (M : ModuleCat.FiniteProjective.{u, v} R) :
    genericRank.{u, v} R (projectiveOf R M) =
      (Module.finrank R M.obj : ℤ) := sorry

/-- Projective generic rank sends a virtual free projective class to its
integer coefficient. -/
@[simp, stacks 0FJ8 "projective generic rank of virtual free classes"]
theorem genericRank_free (n : ℤ) :
    genericRank.{u, u} R (free R n) = n := sorry

end CategoryTheory.ModuleCat.K0.Projective

namespace CategoryTheory.ModuleCat.K0.Finite

variable (R : Type u) [CommRing R] [IsDomain R]

/-- Generic rank commutes with the canonical comparison `K₀(R) →+ K'_0(R)`. -/
@[stacks 0FJ8 "generic rank and the projective-to-finite comparison"]
theorem genericRank_comp_projectiveToFinite :
    (genericRank.{u, v} R).comp (projectiveToFinite.{u, v} R) =
      Projective.genericRank.{u, v} R := sorry

end CategoryTheory.ModuleCat.K0.Finite
