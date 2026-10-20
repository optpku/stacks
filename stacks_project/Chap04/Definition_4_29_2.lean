/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Embedding
public import ReasLib.CategoryTheory.Bicategory.LocalProperties
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe wB vB uB wC vC uC

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable (F : StrictPseudofunctor B C)

/-
Definition 4.29.2: a strict pseudofunctor presents a sub-`2`-category when it is
injective on objects and each induced functor on a hom category is an ordinary
equality-sensitive embedding.

The reusable owner is stated for bicategories: strict pseudofunctoriality supplies closure under
identities and horizontal composition, while `StrictPseudofunctor.IsEmbedding` records injectivity
on objects and `1`-morphisms together with faithfulness on `2`-morphisms. This presentation-level
condition remains distinct from the invariant predicates
`Pseudofunctor.IsLocallyFullyFaithful` and `Pseudofunctor.IsLocallyEquivalence`.
-/
@[stacks 02X7 "sub-2-categories as strict pseudofunctor embeddings"]
#check (F.IsEmbedding : Prop)

/- Companion recall: ordinary categorical embeddings use the same equality-sensitive convention. -/
#check Functor.IsEmbedding

/- Companion recall: selecting only objects gives the canonical full subbicategory. -/
#check ObjectProperty.FullSubbicategory

/- Companion recall: selecting both objects and `1`-morphisms gives a locally induced bicategory. -/
#check Bicategory.LocallyInducedBicategory

/- Companion recall: invariant local full faithfulness is deliberately weaker than strict
injectivity on objects and `1`-morphisms. -/
#check Pseudofunctor.IsLocallyFullyFaithful

end CategoryTheory
