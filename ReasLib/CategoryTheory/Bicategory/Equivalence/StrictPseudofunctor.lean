/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Pseudofunctor.Mapping
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Composition

/-!
# Strict pseudofunctors and bicategorical equivalences

The strict specialization of the generic equivalence action. Its preservation
laws are equalities of equivalence data, unlike the mate isomorphisms needed
for arbitrary pseudofunctors.
-/

@[expose] public section

universe w v u w' v' u' w'' v'' u''

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace StrictPseudofunctor

variable {C : Type u'} [Bicategory.{w', v'} C]
variable {x y : B}

/-- A strict pseudofunctor maps a bicategorical equivalence to a bicategorical equivalence.

This specialization mirrors `StrictPseudofunctor.mapAdjunction` while retaining the full
invertible unit and counit API. -/
@[stacks 0040 "map a bicategorical equivalence through a strict pseudofunctor"]
def mapEquivalence (F : StrictPseudofunctor B C) (e : x ≌ y) :
    F.obj x ≌ F.obj y :=
  F.toPseudofunctor.mapEquivalence e

/-- The forward morphism of an equivalence mapped by a strict pseudofunctor. -/
@[simp]
theorem mapEquivalence.hom
    (F : StrictPseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).hom = F.map e.hom := sorry
/- Proof strategy: unfold the strict specialization and apply
`Pseudofunctor.mapEquivalence.hom`. -/

/-- The inverse morphism of an equivalence mapped by a strict pseudofunctor. -/
@[simp]
theorem mapEquivalence.inv
    (F : StrictPseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).inv = F.map e.inv := sorry
/- Proof strategy: unfold the strict specialization and apply
`Pseudofunctor.mapEquivalence.inv`. -/

/-- The unit of an equivalence mapped by a strict pseudofunctor is the generic mapped unit. -/
@[simp]
theorem mapEquivalence.unit
    (F : StrictPseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso F.toPseudofunctor e := sorry
/- Proof strategy: unfold the strict specialization and apply
`Pseudofunctor.mapEquivalence.unit`. -/

/-- The counit of an equivalence mapped by a strict pseudofunctor is the generic mapped
counit. -/
@[simp]
theorem mapEquivalence.counit
    (F : StrictPseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).counit =
      Pseudofunctor.mapEquivalence.counitIso F.toPseudofunctor e := sorry
/- Proof strategy: unfold the strict specialization and apply
`Pseudofunctor.mapEquivalence.counit`. -/

/-- Forgetting invertibility from a strict-pseudofunctor image recovers the strict mapped
adjunction. -/
@[simp]
theorem mapEquivalence.toAdjunction
    (F : StrictPseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).toAdjunction =
      F.mapAdjunction e.toAdjunction := sorry
/- Proof strategy: unfold the strict specialization and use the generic
`Pseudofunctor.mapEquivalence.toAdjunction`. -/

/-- Passing an equivalence mapped by a strict pseudofunctor to `Bicategory.Adj` agrees with
the canonical adjunction action of its underlying pseudofunctor. -/
@[simp]
theorem mapEquivalence.toAdjHom
    (F : StrictPseudofunctor B C) (e : x ≌ y) :
    (F.mapEquivalence e).toAdjHom =
      F.toPseudofunctor.mapAdj.map e.toAdjHom := sorry

/-- A strict pseudofunctor preserves the identity bicategorical equivalence as an equality of
equivalence data. -/
@[simp]
theorem mapEquivalence.id
    (F : StrictPseudofunctor B C) (x : B) :
    F.mapEquivalence (Bicategory.Equivalence.id x) =
      Bicategory.Equivalence.id (F.obj x) := sorry

/-- A strict pseudofunctor commutes with reversal of bicategorical equivalences as an equality
of equivalence data. -/
@[simp]
theorem mapEquivalence.symm
    (F : StrictPseudofunctor B C) (e : x ≌ y) :
    F.mapEquivalence e.symm =
      (F.mapEquivalence e).symm := sorry

/-- A strict pseudofunctor preserves composition of bicategorical equivalences as an equality
of equivalence data. -/
@[simp]
theorem mapEquivalence.trans
    (F : StrictPseudofunctor B C) {z : B}
    (e : x ≌ y) (e' : y ≌ z) :
    F.mapEquivalence (e.trans e') =
      (F.mapEquivalence e).trans (F.mapEquivalence e') := sorry

/-- Mapping an equivalence through the identity strict pseudofunctor recovers the original
equivalence data. -/
@[simp]
theorem id_mapEquivalence (e : x ≌ y) :
    (StrictPseudofunctor.id B).mapEquivalence e = e := sorry

section Composition

variable {D : Type u''} [Bicategory.{w'', v''} D]

/-- Mapping an equivalence through a composite strict pseudofunctor agrees with iterated
mapping as an equality of equivalence data. -/
@[simp]
theorem comp_mapEquivalence
    (F : StrictPseudofunctor B C)
    (G : StrictPseudofunctor C D) (e : x ≌ y) :
    (F.comp G).mapEquivalence e =
      G.mapEquivalence (F.mapEquivalence e) := sorry

end Composition

end StrictPseudofunctor

end CategoryTheory
