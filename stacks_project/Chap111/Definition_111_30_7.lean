/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Definition_111_30_7_Acyclic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

/- Definition 111.30.7: in an abelian category `𝒜`, a cochain complex `K` of `Filᶠ(𝒜)` is
filtered acyclic when for every `p : ℤ` the graded-piece complex `gr^p(K)` is acyclic. The
reusable cochain-level owner is `FilteredObject.Finite.CochainComplex.acyclic`. -/
@[stacks 028E] #check
  (@FilteredObject.Finite.CochainComplex.acyclic :
    {C : Type u} → [Category.{v} C] → [Abelian C] →
      CochainComplex (FilteredObject.Finite.category C) ℤ → Prop)
