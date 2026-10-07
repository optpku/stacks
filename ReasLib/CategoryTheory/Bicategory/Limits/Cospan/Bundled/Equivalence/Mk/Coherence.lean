module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Equivalence.Mk

/-!
# Coherence computations for componentwise cospan equivalences

This file exposes the unit, counit, and inverse generating comparisons of
`Cospan.equivalenceMk`. The bundled unit and counit are exactly the modifications of the
underlying walking-cospan equivalence, while the inverse comparisons are the canonical mates
constructed by `Pseudofunctor.StrongTrans.PointwiseEquivalence`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {S T : Cospan B}

variable (leftEquiv : S.left ≌ T.left)
variable (rightEquiv : S.right ≌ T.right)
variable (baseEquiv : S.base ≌ T.base)
variable (leftComparison : leftEquiv.hom ≫ T.fst ≅ S.fst ≫ baseEquiv.hom)
variable (rightComparison : rightEquiv.hom ≫ T.snd ≅ S.snd ≫ baseEquiv.hom)

/-- The underlying forward unit modification of `equivalenceMk` is the forward unit of its
walking-cospan equivalence. -/
@[simp]
theorem equivalenceMk.unit.hom.toModification :
    (equivalenceMk
      leftEquiv rightEquiv baseEquiv leftComparison rightComparison).unit.hom.hom =
      (CospanTransform.equivalenceMk
        leftEquiv rightEquiv baseEquiv leftComparison rightComparison).unit.hom := sorry

/-- The underlying inverse unit modification of `equivalenceMk` is the inverse unit of its
walking-cospan equivalence. -/
@[simp]
theorem equivalenceMk.unit.inv.toModification :
    (equivalenceMk
      leftEquiv rightEquiv baseEquiv leftComparison rightComparison).unit.inv.hom =
      (CospanTransform.equivalenceMk
        leftEquiv rightEquiv baseEquiv leftComparison rightComparison).unit.inv := sorry

/-- The underlying forward counit modification of `equivalenceMk` is the forward counit of
its walking-cospan equivalence. -/
@[simp]
theorem equivalenceMk.counit.hom.toModification :
    (equivalenceMk
      leftEquiv rightEquiv baseEquiv leftComparison rightComparison).counit.hom.hom =
      (CospanTransform.equivalenceMk
        leftEquiv rightEquiv baseEquiv leftComparison rightComparison).counit.hom := sorry

/-- The underlying inverse counit modification of `equivalenceMk` is the inverse counit of
its walking-cospan equivalence. -/
@[simp]
theorem equivalenceMk.counit.inv.toModification :
    (equivalenceMk
      leftEquiv rightEquiv baseEquiv leftComparison rightComparison).counit.inv.hom =
      (CospanTransform.equivalenceMk
        leftEquiv rightEquiv baseEquiv leftComparison rightComparison).counit.inv := sorry

/-- The left generating comparison of the inverse of `equivalenceMk` is the canonical mate of
the supplied left comparison. -/
@[simp]
theorem equivalenceMk.inv.leftIso :
    Hom.leftIso
        (equivalenceMk
          leftEquiv rightEquiv baseEquiv leftComparison rightComparison).inv =
      (Pseudofunctor.StrongTrans.PointwiseEquivalence.inverse.naturalityIso
        (CospanTransform.pointwiseEquivalenceMk
          leftEquiv rightEquiv baseEquiv leftComparison rightComparison)
        (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)).symm := sorry

/-- The right generating comparison of the inverse of `equivalenceMk` is the canonical mate
of the supplied right comparison. -/
@[simp]
theorem equivalenceMk.inv.rightIso :
    Hom.rightIso
        (equivalenceMk
          leftEquiv rightEquiv baseEquiv leftComparison rightComparison).inv =
      (Pseudofunctor.StrongTrans.PointwiseEquivalence.inverse.naturalityIso
        (CospanTransform.pointwiseEquivalenceMk
          leftEquiv rightEquiv baseEquiv leftComparison rightComparison)
        (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)).symm := sorry

/- This module introduces only theorem statements. All non-`Prop` unit, counit, and mate data
are owned by `CospanTransform.pointwiseEquivalenceMk` and the induced-bicategory lift. -/

end CategoryTheory.Bicategory.Cospan
