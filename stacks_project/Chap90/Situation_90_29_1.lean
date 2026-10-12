/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Situation_90_29_1_Pullback
import StacksCheckRecall

/-!
# Change of residue field

A finite tower `Λ → k → l` of fields induces the comparison functor
`C_{Λ, l} ⟶ C_{Λ, k}` sending `B` to `B ×_l k`. Reindexing a category cofibered
in groupoids over `C_{Λ, k}` along that functor yields `p_{l/k}` over `C_{Λ, l}`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)

/- Situation 90.29.1 (1): the comparison functor C_{Λ, l} ⟶ C_{Λ, k} sends B to
B ×_l k. -/
@[stacks 07W8] #check (residueChangeFunctor Λ k l :
  ArtinianLocalAlgCat Λ l ⥤ ArtinianLocalAlgCat Λ k)

/- Situation 90.29.1 (2): a category cofibered in groupoids p : F ⥤ C_{Λ, k}
reindexes to p_{l/k} : F_{l/k} ⥤ C_{Λ, l}. -/
@[stacks 07W8] #check (residueChangeOver Λ k l p :
  residueChangeTotal Λ k l p ⥤ ArtinianLocalAlgCat Λ l)
