/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.Equivalence
import StacksCheckRecall

/-!
@stack 019E

# Source-facing recall for Lemma 14.24.1

The normalized Moore complex is the forward functor of the Dold--Kan equivalence. Its
faithfulness and reflection properties are therefore canonical functor instances.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Abelian.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Lemma 14.24.1 (1): the normalized Moore complex functor is faithful. -/
@[stacks 019E]
#check (inferInstance : (N : SimplicialObject A ⥤ ChainComplex A ℕ).Faithful)

/- Lemma 14.24.1 (2): the normalized Moore complex functor reflects isomorphisms. -/
@[stacks 019E]
#check (inferInstance : (N : SimplicialObject A ⥤ ChainComplex A ℕ).ReflectsIsomorphisms)

/- Lemma 14.24.1 (3): the normalized Moore complex functor reflects monomorphisms. -/
@[stacks 019E]
#check (inferInstance : (N : SimplicialObject A ⥤ ChainComplex A ℕ).ReflectsMonomorphisms)

/- Lemma 14.24.1 (4): the normalized Moore complex functor reflects epimorphisms. -/
@[stacks 019E]
#check (inferInstance : (N : SimplicialObject A ⥤ ChainComplex A ℕ).ReflectsEpimorphisms)

#check (equivalence_functor (A := A) :
  (equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor = N)

end CategoryTheory.Abelian.DoldKan
