module

public import stacks_project.Chap90.«90_29_1_1_Comparison»
import StacksCheckRecall

/-!
# Comparison functor on change of residue field

Situation 90.29.1: a finite tower `Λ → k → l` of fields induces the comparison
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
@[stacks 07W9] #check (residueChangeFunctor Λ k l : ArtinianLocalAlgCat Λ l ⥤ ArtinianLocalAlgCat Λ k)
