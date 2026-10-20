/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic equivalence data for bicategorical cospans

This leaf owns the walking-cospan specialization of generic pointwise-equivalence data.  The
three vertex equivalences and their component comparison isomorphisms are retained explicitly;
the inverse transformation and coherence are supplied by the neutral mate construction.
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

namespace Implementation

/-- Assemble equivalences at the three vertices of the walking cospan. -/
private def pointwiseEquivalenceApp
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z') :
    ∀ a : LocallyDiscrete Limits.WalkingCospan,
      (cospan f g).obj a ≌ (cospan f' g').obj a
  | ⟨none⟩ => baseEquiv
  | ⟨some Limits.WalkingPair.left⟩ => leftEquiv
  | ⟨some Limits.WalkingPair.right⟩ => rightEquiv

/-- Assemble the invertible `2`-cells aligning the three vertex equivalences
with the components of a cospan transformation. -/
private def pointwiseEquivalenceApp.homIso
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    ∀ a : LocallyDiscrete Limits.WalkingCospan,
      (pointwiseEquivalenceApp leftEquiv rightEquiv baseEquiv a).hom ≅
        ψ.app a
  | ⟨none⟩ => baseHomIso
  | ⟨some Limits.WalkingPair.left⟩ => leftHomIso
  | ⟨some Limits.WalkingPair.right⟩ => rightHomIso

end Implementation

/-- Equip a cospan transformation with pointwise equivalence data supplied at its three
vertices.

This is the walking-cospan facade for
`Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents`. -/
@[stacks 0040 "pointwise equivalence data for a bicategorical cospan transformation"]
def pointwiseEquivalence
    (ψ : CospanTransform f g f' g')
    (leftEquiv : x ≌ x') (rightEquiv : y ≌ y') (baseEquiv : z ≌ z')
    (leftHomIso : leftEquiv.hom ≅ ψ.left)
    (rightHomIso : rightEquiv.hom ≅ ψ.right)
    (baseHomIso : baseEquiv.hom ≅ ψ.base) :
    Pseudofunctor.StrongTrans.PointwiseEquivalence ψ :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (Implementation.pointwiseEquivalenceApp leftEquiv rightEquiv baseEquiv)
    (Implementation.pointwiseEquivalenceApp.homIso ψ leftEquiv rightEquiv baseEquiv
      leftHomIso rightHomIso baseHomIso)

/- Data audit (mathlib 4.32): `pointwiseEquivalence` delegates to the generic
`PointwiseEquivalence.ofComponents` and retains all three supplied equivalences and comparison
isomorphisms as explicit non-`Prop` data. Any deferred content is inherited triangle/coherence
proof data; no witness is selected by this cospan specialization. -/

end CategoryTheory.Bicategory.CospanTransform
