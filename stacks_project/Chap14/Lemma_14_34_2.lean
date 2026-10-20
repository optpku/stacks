/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Construction
import StacksCheckRecall

@[expose] public section

/-!
@stack 08NC

# The standard simplicial resolution of an adjunction

This source-facing file records the two clauses of Lemma 14.34.2. The reusable construction is
the canonical resolution owned by `CategoryTheory.Comonad`.
-/

open CategoryTheory

universe uA uS vA vS

namespace CategoryTheory

variable {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
variable {U : S ⥤ A} {V : A ⥤ S} (adj : U ⊣ V)

/- The reusable owner bundles the simplicial resolution and its augmentation, so downstream
whiskering and evaluation do not have to reassemble the two source clauses. -/
@[stacks 08NC "Lemma 14.34.2: bundled augmented resolution"]
#check (Comonad.simplicialResolution.augmented adj.toComonad :
  SimplicialObject.Augmented (A ⥤ A))

/- Lemma 14.34.2 (1): the iterated comonad system attached to `adj` is the canonical simplicial
object of endofunctors. -/
@[stacks 08NC "Lemma 14.34.2 (1)"]
#check (Comonad.simplicialResolution adj.toComonad : SimplicialObject (A ⥤ A))

@[stacks 08NC "Lemma 14.34.2 (1): realization witness"]
#check (Comonad.simplicialResolution.realization adj.toComonad :
  adj.toComonad.Realizes adj.toComonad.simplicialResolution)

/- Lemma 14.34.2 (2): its degree-zero counit extends to the canonical augmentation toward the
constant identity endofunctor. -/
@[stacks 08NC "Lemma 14.34.2 (2)"]
#check (Comonad.simplicialResolution.augmentation adj.toComonad :
  Comonad.simplicialResolution adj.toComonad ⟶
    (SimplicialObject.const (A ⥤ A)).obj (𝟭 A))

/- Companion strengthening: the prescribed objects, faces, and degeneracies determine this
realization uniquely. -/
#check (Adjunction.SimplicialResolution.obj adj)
#check (Adjunction.SimplicialResolution.face adj)
#check (Adjunction.SimplicialResolution.degeneracy adj)
#check (Adjunction.SimplicialResolution.augmentation.app_zero adj)
#check (Comonad.Realizes.existsUnique adj.toComonad :
  ∃! X : SimplicialObject (A ⥤ A), adj.toComonad.Realizes X)

end CategoryTheory
