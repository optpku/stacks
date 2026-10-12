/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import stacks_project.Chap90.Definition_90_3_1_Classical
import StacksCheckRecall

/-!
# The base category of Artinian local algebras
-/

@[expose] public section

universe u

/- Definition 90.3.1 (1): the category of Artinian local `Λ`-algebras equipped with a
`Λ`-algebra identification of the residue field with a finite `Λ`-field `k`. -/
@[stacks 06GC]
#check (ArtinianLocalAlgCat :
  (Λ k : Type u) → [CommRing Λ] → [IsNoetherianRing Λ] → [Field k] →
    [Algebra Λ k] → [Module.Finite Λ k] → Type (u + 1))

#check ArtinianLocalAlgCat.Hom
#check ArtinianLocalAlgCat.category

/- Definition 90.3.1 (2): the classical case, when `Λ` is a Noetherian complete local
ring and `k` is its residue field. -/
@[stacks 06GC]
#check (ArtinianLocalAlgCat.IsClassical :
  (Λ k : Type u) → [CommRing Λ] → [IsNoetherianRing Λ] → [Field k] →
    [Algebra Λ k] → [Module.Finite Λ k] → Prop)
