module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Equivalence.StrictPseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans

/-!
# Pointwise equivalences of pseudofunctors

Objectwise evaluation of bicategorical equivalences in a pseudofunctor bicategory.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Bicategory.Equivalence

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G H : Pseudofunctor B D}

/-- Evaluate an equivalence in a pseudofunctor bicategory at an object of the source
bicategory.

This is the equivalence-level counterpart of `Pseudofunctor.evaluationAt.map` and
`Pseudofunctor.StrongTrans.isoApp`. It is obtained by applying the strict evaluation
pseudofunctor to the supplied bicategorical equivalence. -/
@[stacks 0040 "evaluate a pseudofunctor equivalence at an object"]
def app (e : F ≌ G) (a : B) : F.obj a ≌ G.obj a :=
  (Pseudofunctor.evaluationAt D a).mapEquivalence e

/-- The forward morphism of a pointwise diagram equivalence is the corresponding component of
the forward strong transformation. -/
@[simp]
theorem app.hom (e : F ≌ G) (a : B) :
    (e.app a).hom = e.hom.app a := sorry
/- Proof strategy: unfold `app`; combine `StrictPseudofunctor.mapEquivalence.hom` with
`Pseudofunctor.evaluationAt.map`. -/

/-- The inverse morphism of a pointwise diagram equivalence is the corresponding component of
the inverse strong transformation. -/
@[simp]
theorem app.inv (e : F ≌ G) (a : B) :
    (e.app a).inv = e.inv.app a := sorry
/- Proof strategy: unfold `app`; combine `StrictPseudofunctor.mapEquivalence.inv` with
`Pseudofunctor.evaluationAt.map`. -/

/-- The unit of a pointwise diagram equivalence is the component of the diagram-equivalence
unit. -/
@[simp]
theorem app.unit (e : F ≌ G) (a : B) :
    (e.app a).unit =
      Pseudofunctor.StrongTrans.isoApp e.unit a := sorry
/- Proof strategy: unfold `app` and the mapped unit. The identity and composition comparisons
of `evaluationAt` are identity isomorphisms, while its map on modifications is component
evaluation. -/

/-- The counit of a pointwise diagram equivalence is the component of the diagram-equivalence
counit. -/
@[simp]
theorem app.counit (e : F ≌ G) (a : B) :
    (e.app a).counit =
      Pseudofunctor.StrongTrans.isoApp e.counit a := sorry
/- Proof strategy: unfold `app` and the mapped counit, then use the strict computation API of
`evaluationAt`. -/

/-- The forward unit cell of a pointwise diagram equivalence is the corresponding component of
the forward unit modification. -/
@[simp]
theorem app.unit.hom (e : F ≌ G) (a : B) :
    (e.app a).unit.hom = e.unit.hom.as.app a := sorry
/- Proof strategy: rewrite with `app.unit` and
`Pseudofunctor.StrongTrans.isoApp.hom`. -/

/-- The inverse unit cell of a pointwise diagram equivalence is the corresponding component of
the inverse unit modification. -/
@[simp]
theorem app.unit.inv (e : F ≌ G) (a : B) :
    (e.app a).unit.inv = e.unit.inv.as.app a := sorry
/- Proof strategy: rewrite with `app.unit` and
`Pseudofunctor.StrongTrans.isoApp.inv`. -/

/-- The forward counit cell of a pointwise diagram equivalence is the corresponding component
of the forward counit modification. -/
@[simp]
theorem app.counit.hom (e : F ≌ G) (a : B) :
    (e.app a).counit.hom = e.counit.hom.as.app a := sorry
/- Proof strategy: rewrite with `app.counit` and
`Pseudofunctor.StrongTrans.isoApp.hom`. -/

/-- The inverse counit cell of a pointwise diagram equivalence is the corresponding component
of the inverse counit modification. -/
@[simp]
theorem app.counit.inv (e : F ≌ G) (a : B) :
    (e.app a).counit.inv = e.counit.inv.as.app a := sorry
/- Proof strategy: rewrite with `app.counit` and
`Pseudofunctor.StrongTrans.isoApp.inv`. -/

/-- The adjunction underlying a pointwise diagram equivalence is evaluation of the adjunction
underlying the diagram equivalence. -/
@[simp]
theorem app.toAdjunction (e : F ≌ G) (a : B) :
    (e.app a).toAdjunction =
      (Pseudofunctor.evaluationAt D a).mapAdjunction
        e.toAdjunction := sorry
/- Proof strategy: unfold `app` and apply
`StrictPseudofunctor.mapEquivalence.toAdjunction`. -/

/-- Pointwise evaluation preserves identity bicategorical equivalences. -/
@[simp]
theorem app.id (F : Pseudofunctor B D) (a : B) :
    (Bicategory.Equivalence.id F).app a =
      Bicategory.Equivalence.id (F.obj a) := sorry
/- Proof strategy: extensionality; use `app.hom`, `app.inv`, `app.unit`, and `app.counit`,
then reduce pointwise evaluation of identity strong transformations and modifications. -/

/-- Pointwise evaluation commutes with reversal of bicategorical equivalences. -/
@[simp]
theorem app.symm (e : F ≌ G) (a : B) :
    e.symm.app a = (e.app a).symm := sorry
/- Proof strategy: extensionality and the pointwise formulas for the forward and inverse
transformations, unit, and counit. -/

/-- Pointwise evaluation commutes with composition of bicategorical equivalences. -/
@[simp]
theorem app.trans (e : F ≌ G) (e' : G ≌ H) (a : B) :
    (e.trans e').app a = (e.app a).trans (e'.app a) := sorry
/- Proof strategy: extensionality; evaluate the composite strong transformations and the
canonical composite unit and counit componentwise. -/

/- Data audit (mathlib 4.32): `Bicategory.Equivalence.app` uses the explicit
`StrictPseudofunctor.mapEquivalence` owner. Its forward and inverse morphisms are the two strong
transformation components, and both directions of its unit and counit are the corresponding
modification components. Any `sorryAx` is confined to triangle and compatibility proofs. -/

end Bicategory.Equivalence

end CategoryTheory
