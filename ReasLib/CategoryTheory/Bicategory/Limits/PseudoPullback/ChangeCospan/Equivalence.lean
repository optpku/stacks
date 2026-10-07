module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Equivalence

/-!
# Equivalences induced by changing cospan

This module packages the global consequences of the readable changed-cospan pseudofunctor:
equivalences of walking-cospan diagrams induce biequivalences of readable cone bicategories and
preserve the bilimit property.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- Changing a readable pseudo-pullback cospan along a pointwise-equivalence cospan
transformation is a biequivalence of cone bicategories.

This is the primary transport interface: callers that already have vertexwise equivalences use
`CospanTransform.pointwiseEquivalence` or `CospanTransform.pointwiseEquivalenceMk` directly and
need not first package a functor-bicategory equivalence. -/
theorem changeCospan.isBiequivalence
    (ψ : CospanTransform f g f' g')
    (h : Pseudofunctor.StrongTrans.PointwiseEquivalence ψ) :
    Pseudofunctor.IsBiequivalence (changeCospan.pseudofunctor ψ) := sorry
/- Proof strategy: compare with `PseudoCone.postcompose ψ` through the explicit
readable/generic presentation biequivalences, then apply `PseudoCone.postcompose_isBiequivalence`.
-/

/-- Changing a readable pseudo-pullback cospan along an equivalence of walking-cospan
diagrams is a biequivalence of cone bicategories. -/
instance changeCospan.isBiequivalence_of_equivalence
    (e : Bicategory.cospan f g ≌ Bicategory.cospan f' g') :
    Pseudofunctor.IsBiequivalence
      (changeCospan.pseudofunctor e.hom) := sorry
/- Proof strategy: compare with `PseudoCone.postcompose e.hom` through the explicit
readable/generic presentation biequivalences, then apply `PseudoCone.postcomposeIsBiequivalence`.
-/

/-- Changing a readable pseudo-pullback cospan along a pointwise-equivalence cospan
transformation preserves the bilimit property. -/
theorem changeCospan.preserves_isBilimit
    (ψ : CospanTransform f g f' g')
    (h : Pseudofunctor.StrongTrans.PointwiseEquivalence ψ)
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (S.changeCospan ψ).IsBilimit := sorry
/- Proof strategy: use `changeCospan.toPseudoCone` and
`PseudoCone.postcomposeObj_isBilimit`. -/

/-- Changing a readable pseudo-pullback cospan along a pointwise-equivalence cospan
transformation reflects the bilimit property. -/
theorem changeCospan.reflects_isBilimit
    (ψ : CospanTransform f g f' g')
    (h : Pseudofunctor.StrongTrans.PointwiseEquivalence ψ)
    (S : PseudoPullbackCone f g) [(S.changeCospan ψ).IsBilimit] :
    S.IsBilimit := sorry
/- Proof strategy: use `changeCospan.toPseudoCone` and
`PseudoCone.isBilimit_of_postcomposeObj`. -/

/-- Changing a readable pseudo-pullback cospan along a pointwise-equivalence cospan
transformation preserves and reflects the bilimit property.

This is the pointwise form of the transport theorem. The equivalence-packaged specialization
below remains useful when the diagram equivalence is already the available datum. -/
theorem changeCospan.isBilimit_iff
    (ψ : CospanTransform f g f' g')
    (h : Pseudofunctor.StrongTrans.PointwiseEquivalence ψ)
    (S : PseudoPullbackCone f g) :
    (S.changeCospan ψ).IsBilimit ↔ S.IsBilimit := sorry
/- Proof strategy: use `changeCospan.toPseudoCone` and
`PseudoCone.postcomposeObj_isBilimit_iff`. -/

/-- Changing a readable pseudo-pullback cospan along an equivalence of walking-cospan diagrams
preserves and reflects the bilimit property. -/
theorem changeCospan.isBilimit_iff_of_equivalence
    (e : Bicategory.cospan f g ≌ Bicategory.cospan f' g')
    (S : PseudoPullbackCone f g) :
    (S.changeCospan e.hom).IsBilimit ↔ S.IsBilimit := sorry
/- Proof strategy: use `changeCospan.toPseudoCone` and
`PseudoCone.postcomposeObj_isBilimit_iff`. -/

/- Data audit (mathlib 4.32): `changeCospan.fac`, `changeCospan.map`,
`changeCospan.map₂`, `changeCospan.mapId`, `changeCospan.mapComp`, and
`changeCospan.pseudofunctor` have explicit object, morphism, modification, inverse, unit, and
composition data. `#print axioms` on the presentation comparison and changed-cospan
pseudofunctor reports `[propext, sorryAx, Classical.choice, Quot.sound]`; source inspection
confines `sorryAx` to Prop-valued naturality, compatibility, inverse-law, equivalence, and
pseudofunctor-coherence fields. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
