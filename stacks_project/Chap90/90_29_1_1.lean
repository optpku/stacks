/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange
import StacksCheckRecall

/-!
# Comparison functor on change of residue field

Situation 90.29.1: a finite tower `Λ → k → l` with `Λ` Noetherian and `k`, `l`
fields induces the comparison
functor `C_{Λ, l} ⟶ C_{Λ, k}` sending `B` to the fibre product `B ×_l k`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]

/- 90.29.1.1 The comparison functor C_{Λ, l} ⟶ C_{Λ, k} on objects is
B ↦ B ×_l k, the ring fibre product of B → l along k → l. -/
@[stacks 07W9] #check
  (ArtinianLocalAlgCat.residueChangeFunctor Λ k l :
    ArtinianLocalAlgCat Λ l ⥤ ArtinianLocalAlgCat Λ k)
