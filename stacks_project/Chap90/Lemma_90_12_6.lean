/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.SquareZeroDerivation
import StacksCheckRecall

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

/- Lemma 90.12.6 (1): The canonical derivation maps are `k`-linear under (S2). -/
@[stacks 06SU]
#check (CategoryTheory.Functor.isoClassOfDerivation_isLinearMap p V :
  IsLinearMap k (CategoryTheory.Functor.isoClassOfDerivation p V))

/- Lemma 90.12.6 (2): The canonical derivation action is translation by `γ_V(D)`. -/
@[stacks 06SU]
#check (CategoryTheory.Functor.squareZeroDerivationAction_eq_add p V :
  ∀ (D : Derivation Λ k V) (x : (fiberIsoClassFunctor p).obj (squareZero Λ k V)),
    CategoryTheory.Functor.squareZeroDerivationAction p V D x =
      x + CategoryTheory.Functor.isoClassOfDerivation p V D)
