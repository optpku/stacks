/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import stacks_project.Chap90.Lemma_90_12_6_Action
public import stacks_project.Chap90.Lemma_90_12_6_Derivation

/-!
# Lemma 90.12.6

If `F` is a predeformation category whose associated isomorphism-class functor
`F-bar` satisfies (S2), then the maps `γ_V` are `k`-linear and
`a_V(D, x) = x + γ_V(D)`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Module Λ V] [IsScalarTower Λ k V]

namespace CategoryTheory.Functor

/-- Lemma 90.12.6 (1): Let `F` be a predeformation category over `C_Λ`. If
`F-bar` has (S2) then the maps `γ_V` are `k`-linear. -/
@[stacks 06SU]
theorem isoClassOfDerivation_isLinearMap :
    IsLinearMap k (isoClassOfDerivation p V) := sorry

/-- Lemma 90.12.6 (2): Let `F` be a predeformation category over `C_Λ`. If
`F-bar` has (S2) then `a_V(D, x) = x + γ_V(D)`. -/
@[stacks 06SU]
theorem squareZeroDerivationAction_eq_add (D : Derivation Λ k V)
    (x : (fiberIsoClassFunctor p).obj (squareZero Λ k V)) :
    squareZeroDerivationAction p V D x = x + isoClassOfDerivation p V D := sorry

end CategoryTheory.Functor
