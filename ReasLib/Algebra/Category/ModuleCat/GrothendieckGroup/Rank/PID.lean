module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.Domain
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Grothendieck Rank over a Principal Ideal Domain

Over a principal ideal domain, every finite-module Grothendieck class is its
generic rank times `[R]`. This supplies explicit inverse maps and identifies
both `K₀(R)` and `K'_0(R)` with `ℤ`.

@stack 0FJ8
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.K0.Finite

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Over a PID, the virtual free class of the generic rank of a finite-module
Grothendieck class is the original class. -/
@[simp, stacks 0FJ8 "finite-module classes are determined by generic rank"]
theorem free_genericRank (x : finite.{u, u} R) :
    free R (genericRank.{u, u} R x) = x := sorry

/-- Generic rank identifies the finite-module Grothendieck group of a PID with
`ℤ`; the inverse is explicitly the virtual free-class map. -/
@[stacks 0FJ8 "finite-module K0 of a PID"]
def genericRankEquiv : finite.{u, u} R ≃+ ℤ where
  toFun := genericRank R
  invFun := free R
  left_inv := free_genericRank R
  right_inv := genericRank_free R
  map_add' := (genericRank R).map_add

/-- The finite-module generic-rank equivalence acts by `genericRank`. -/
@[simp]
theorem genericRankEquiv_apply (x : finite.{u, u} R) :
    genericRankEquiv R x = genericRank R x := sorry

/-- The inverse finite-module generic-rank equivalence is `free`. -/
@[simp]
theorem genericRankEquiv_symm_apply (n : ℤ) :
    (genericRankEquiv R).symm n = free R n := sorry

/-- The generic-rank homomorphism on finite modules is bijective over a PID. -/
@[stacks 0FJ8 "bijectivity of finite-module generic rank"]
theorem genericRank_bijective :
    Function.Bijective (genericRank.{u, u} R) := sorry

end CategoryTheory.ModuleCat.K0.Finite

namespace CategoryTheory.ModuleCat.K0.Projective

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Over a PID, the virtual free class of projective generic rank is the
original projective Grothendieck class. -/
@[simp, stacks 0FJ8 "projective classes are determined by generic rank"]
theorem free_genericRank (x : projective.{u, u} R) :
    free R (genericRank.{u, u} R x) = x := sorry

/-- Projective generic rank identifies `K₀(R)` of a PID with `ℤ`; its inverse
is explicitly the virtual free-projective-class map. -/
@[stacks 0FJ8 "projective K0 of a PID"]
def genericRankEquiv : projective.{u, u} R ≃+ ℤ where
  toFun := genericRank R
  invFun := free R
  left_inv := free_genericRank R
  right_inv := genericRank_free R
  map_add' := (genericRank R).map_add

/-- The projective generic-rank equivalence acts by `genericRank`. -/
@[simp]
theorem genericRankEquiv_apply (x : projective.{u, u} R) :
    genericRankEquiv R x = genericRank R x := sorry

/-- The inverse projective generic-rank equivalence is `free`. -/
@[simp]
theorem genericRankEquiv_symm_apply (n : ℤ) :
    (genericRankEquiv R).symm n = free R n := sorry

/-- The projective generic-rank homomorphism is bijective over a PID. -/
@[stacks 0FJ8 "bijectivity of projective generic rank"]
theorem genericRank_bijective :
    Function.Bijective (genericRank.{u, u} R) := sorry

end CategoryTheory.ModuleCat.K0.Projective

namespace CategoryTheory.ModuleCat.K0

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Under the two generic-rank equivalences, `projectiveToFinite` acts as the
identity on `ℤ`. -/
@[simp, stacks 0FJ8 "projective-to-finite comparison in generic-rank coordinates"]
theorem genericRankEquiv_projectiveToFinite_apply (x : projective.{u, u} R) :
    Finite.genericRankEquiv R (projectiveToFinite R x) =
      Projective.genericRankEquiv R x := sorry

/-- The projective-to-finite comparison over a PID is the identification
obtained by passing through the two explicit generic-rank equivalences. -/
@[stacks 0FJ8 "projective-to-finite comparison over a PID"]
theorem projectiveToFinite_eq_viaGenericRank :
    projectiveToFinite.{u, u} R =
      (Finite.genericRankEquiv R).symm.toAddMonoidHom.comp
        (Projective.genericRankEquiv R).toAddMonoidHom := sorry

end CategoryTheory.ModuleCat.K0
