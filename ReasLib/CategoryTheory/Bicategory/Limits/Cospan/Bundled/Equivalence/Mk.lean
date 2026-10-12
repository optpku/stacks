/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructing equivalences of bundled bicategorical cospans

Equivalences at the three vertices, together with invertible comparisons for the two cospan
legs, determine an equivalence of bundled cospans. The construction first uses the canonical
walking-cospan constructor `CospanTransform.equivalenceMk`, then changes only its owner through
`Cospan.equivalenceOfDiagram`.

This file records the data-level and generator-level computations. Unit, counit, and inverse
mate computations are layered in `Cospan.Bundled.Equivalence.Mk.Coherence`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T : Cospan B}

/-- Construct an equivalence of bundled cospans from equivalences at the three vertices and
invertible comparisons for the two legs.

No inverse comparison or adjoint-equivalence datum is requested: those are supplied by the
generic pointwise mate construction and the induced-bicategory lift. -/
@[stacks 0040 "bundled-cospan equivalence from component equivalences"]
def equivalenceMk
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    S ≌ T :=
  equivalenceOfDiagram
    (CospanTransform.equivalenceMk
      leftEquiv rightEquiv baseEquiv leftIso rightIso)

/-- The diagram equivalence underlying `equivalenceMk` is the componentwise walking-cospan
equivalence. -/
@[simp]
theorem equivalenceMk.diagramEquivalence
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    diagramEquivalence
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso) =
      CospanTransform.equivalenceMk
        leftEquiv rightEquiv baseEquiv leftIso rightIso := sorry

/-- The complete underlying forward transformation of `equivalenceMk` is the transformation
assembled from the supplied forward maps and comparisons. -/
@[simp]
theorem equivalenceMk.hom.toCospanTransform
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    (equivalenceMk
      leftEquiv rightEquiv baseEquiv leftIso rightIso).hom.hom =
      CospanTransform.mk
        leftEquiv.hom rightEquiv.hom baseEquiv.hom leftIso rightIso := sorry

/-- The complete underlying inverse transformation of `equivalenceMk` is the inverse supplied
by the generic pointwise-equivalence construction. -/
@[simp]
theorem equivalenceMk.inv.toCospanTransform
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    (equivalenceMk
      leftEquiv rightEquiv baseEquiv leftIso rightIso).inv.hom =
      (CospanTransform.equivalenceMk
        leftEquiv rightEquiv baseEquiv leftIso rightIso).inv := sorry

/-- The left-endpoint equivalence of `equivalenceMk` is the supplied equivalence. -/
@[simp]
theorem equivalenceMk.leftEquivalence
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    leftEquivalence
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso) =
      leftEquiv := sorry

/-- The right-endpoint equivalence of `equivalenceMk` is the supplied equivalence. -/
@[simp]
theorem equivalenceMk.rightEquivalence
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    rightEquivalence
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso) =
      rightEquiv := sorry

/-- The common-target equivalence of `equivalenceMk` is the supplied equivalence. -/
@[simp]
theorem equivalenceMk.baseEquivalence
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    baseEquivalence
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso) =
      baseEquiv := sorry

/-- The left component of the forward morphism of `equivalenceMk` is the supplied forward
morphism. -/
@[simp]
theorem equivalenceMk.hom.left
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    Hom.left
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).hom =
      leftEquiv.hom := sorry

/-- The right component of the forward morphism of `equivalenceMk` is the supplied forward
morphism. -/
@[simp]
theorem equivalenceMk.hom.right
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    Hom.right
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).hom =
      rightEquiv.hom := sorry

/-- The base component of the forward morphism of `equivalenceMk` is the supplied forward
morphism. -/
@[simp]
theorem equivalenceMk.hom.base
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    Hom.base
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).hom =
      baseEquiv.hom := sorry

/-- The left generating comparison of the forward morphism of `equivalenceMk` is the supplied
comparison. -/
@[simp]
theorem equivalenceMk.hom.leftIso
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    Hom.leftIso
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).hom =
      leftIso := sorry

/-- The right generating comparison of the forward morphism of `equivalenceMk` is the
supplied comparison. -/
@[simp]
theorem equivalenceMk.hom.rightIso
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    Hom.rightIso
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).hom =
      rightIso := sorry

/-- The left component of the inverse morphism of `equivalenceMk` is the supplied inverse
morphism. -/
@[simp]
theorem equivalenceMk.inv.left
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    Hom.left
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).inv =
      leftEquiv.inv := sorry

/-- The right component of the inverse morphism of `equivalenceMk` is the supplied inverse
morphism. -/
@[simp]
theorem equivalenceMk.inv.right
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    Hom.right
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).inv =
      rightEquiv.inv := sorry

/-- The base component of the inverse morphism of `equivalenceMk` is the supplied inverse
morphism. -/
@[simp]
theorem equivalenceMk.inv.base
    (leftEquiv : S.left ≌ T.left)
    (rightEquiv : S.right ≌ T.right)
    (baseEquiv : S.base ≌ T.base)
    (leftIso : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom) :
    Hom.base
        (equivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).inv =
      baseEquiv.inv := sorry

/- Data and axiom audit (mathlib 4.32):

`equivalenceMk` reuses `CospanTransform.equivalenceMk` and the canonical
`equivalenceOfDiagram` lift. Its three inverse maps and all unit/counit data therefore remain
the supplied or generically constructed data, with no second choice. `#print axioms` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`; `sorryAx` is confined to mate,
triangle/coherence, and wrapper-equality proofs. -/

end CategoryTheory.Bicategory.Cospan
