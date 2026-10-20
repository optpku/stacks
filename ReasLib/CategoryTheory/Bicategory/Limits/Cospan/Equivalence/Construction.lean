/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence constructors for bicategorical cospans

This leaf owns the two source-facing constructors: one consumes an existing cospan
transformation with vertex equivalences, and the other builds the transformation from three
equivalences and the two generating comparisons.  Both delegate to the generic pointwise
equivalence owner, so inverse mates and coherence are not duplicated here.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- A cospan transformation equipped with equivalences at its three components determines an
equivalence of walking-cospan pseudofunctors. -/
@[stacks 0040 "equivalence of cospan diagrams from a pointwise-equivalent transformation"]
def equivalenceOfComponents
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    cospan f g ≌ cospan f' g' :=
  (pointwiseEquivalence ψ leftEquiv rightEquiv baseEquiv
    leftHomIso rightHomIso baseHomIso).toEquivalence

/-- Pointwise equivalence data for the cospan transformation constructed from three vertex
equivalences and two generating comparisons.

This delegates to `pointwiseEquivalence`, hence ultimately to the generic
`PointwiseEquivalence.ofComponents` constructor. -/
@[stacks 0040 "pointwise equivalence from bicategorical cospan components"]
def pointwiseEquivalenceMk
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    Pseudofunctor.StrongTrans.PointwiseEquivalence
      (mk leftEquiv.hom rightEquiv.hom baseEquiv.hom leftIso rightIso) :=
  pointwiseEquivalence
    (mk leftEquiv.hom rightEquiv.hom baseEquiv.hom leftIso rightIso)
    leftEquiv rightEquiv baseEquiv
    (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- Construct an equivalence of walking-cospan diagrams from equivalences at the three vertices
and invertible comparisons on the two generating arrows. -/
@[stacks 0040 "equivalence of bicategorical cospans from component equivalences"]
def equivalenceMk
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftIso : leftEquiv.hom ≫ f' ≅ f ≫ baseEquiv.hom)
    (rightIso : rightEquiv.hom ≫ g' ≅ g ≫ baseEquiv.hom) :
    cospan f g ≌ cospan f' g' :=
  (pointwiseEquivalenceMk leftEquiv rightEquiv baseEquiv leftIso rightIso).toEquivalence

/- Data audit (mathlib 4.32): all constructors retain the supplied equivalences and comparison
isomorphisms. The only deferred fields are the generic mate/coherence propositions; no inverse
component is selected through an opaque witness. -/

end CategoryTheory.Bicategory.CospanTransform
