/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Composition
public import ReasLib.CategoryTheory.Bicategory.HomProperty

/-!
# Equivalences admitted by a bicategorical hom property

An ambient bicategorical equivalence is admissible for a hom property when both its forward
and inverse `1`-morphisms satisfy that property. This condition belongs to the hom property,
independently of the locally induced bicategory it can be used to construct.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open scoped Bicategory

universe w v u u'

namespace Bicategory.HomProperty

variable {B : Type u'} {C : Type u} [Bicategory.{w, v} C]
variable {F : B → C} (Q : HomProperty F)

/-- An ambient equivalence whose forward and inverse `1`-morphisms satisfy a selected
bicategorical hom property. -/
@[stacks 0040 "ambient equivalence admitted by a bicategorical hom property"]
abbrev AdmissibleEquivalence (X Y : B) :=
  { e : F X ≌ F Y // Q X Y e.hom ∧ Q Y X e.inv }

namespace AdmissibleEquivalence

variable {Q} {X Y Z : B}

/-- Bundle an ambient equivalence together with admissibility of its forward and inverse
`1`-morphisms. -/
@[stacks 0040 "construct an equivalence admitted by a hom property"]
def mk (e : F X ≌ F Y) (hom_mem : Q X Y e.hom) (inv_mem : Q Y X e.inv) :
    Q.AdmissibleEquivalence X Y :=
  ⟨e, hom_mem, inv_mem⟩

/-- The ambient equivalence carried by an admissible equivalence. -/
abbrev toEquivalence (e : Q.AdmissibleEquivalence X Y) : F X ≌ F Y :=
  e.1

/-- The forward `1`-morphism of an admissible equivalence satisfies the hom property. -/
theorem hom_mem (e : Q.AdmissibleEquivalence X Y) :
    Q X Y e.toEquivalence.hom := sorry

/-- The inverse `1`-morphism of an admissible equivalence satisfies the hom property. -/
theorem inv_mem (e : Q.AdmissibleEquivalence X Y) :
    Q Y X e.toEquivalence.inv := sorry

/-- The identity equivalence is admissible for a multiplicative hom property. -/
@[stacks 0040 "identity equivalence admitted by a hom property"]
def id (Q : HomProperty F) [Q.IsMultiplicative] (X : B) :
    Q.AdmissibleEquivalence X X :=
  mk (Bicategory.Equivalence.id (F X))
    (IsMultiplicative.id_mem X) (IsMultiplicative.id_mem X)

/-- Reversing an admissible equivalence preserves admissibility. -/
@[stacks 0040 "reverse an equivalence admitted by a hom property"]
def symm (e : Q.AdmissibleEquivalence X Y) : Q.AdmissibleEquivalence Y X :=
  mk e.toEquivalence.symm e.property.2 e.property.1

variable [Q.IsMultiplicative]

/-- The composite of two admissible equivalences is admissible. -/
@[stacks 0040 "compose equivalences admitted by a hom property"]
def trans (e : Q.AdmissibleEquivalence X Y) (e' : Q.AdmissibleEquivalence Y Z) :
    Q.AdmissibleEquivalence X Z :=
  mk (e.toEquivalence.trans e'.toEquivalence)
    (IsMultiplicative.comp_mem e.property.1 e'.property.1)
    (IsMultiplicative.comp_mem e'.property.2 e.property.2)

/- Data and axiom audit (mathlib 4.32): `id` constructs all non-Prop equivalence data
explicitly and is free of `sorryAx`. The data of `symm` and `trans` is inherited from the
ambient bicategorical equivalences; their reported `sorryAx` occurs only in the ambient
triangle/coherence proof fields. Admissibility witnesses themselves are Prop-valued. -/

end AdmissibleEquivalence

end Bicategory.HomProperty

end CategoryTheory
