/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Local complete intersection families of curves

The local complete intersection condition on curve families is represented by
an open of the base under arbitrary scheme base change and is equivalent to
the syntomic condition. Over a field it agrees with the scheme-level local
complete intersection condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves whose structure morphism is a
local complete intersection. -/
def lci (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.IsLocalCompleteIntersection (hom P)

/-- Membership in `lci` is local complete intersection of the structure
morphism. -/
theorem lci_iff {S : Scheme.{u}} (P : Obj S) :
    lci S P ↔ AlgebraicSpace.IsLocalCompleteIntersection (hom P) := Iff.rfl

/-- The local complete intersection property of families of curves is closed
under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_lci (S : Scheme.{u}) :
    (lci S).IsClosedUnderIsomorphisms :=
  sorry

/-- For every family of curves, an open of its base represents the condition
that its pullback is a local complete intersection under every scheme base
change. -/
theorem exists_lci_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
      AlgebraicSpace.IsLocalCompleteIntersection
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) ↔
        Set.range T.hom ⊆ U :=
  sorry

/-- The projection of local complete intersection curve families to their
base schemes is fibred in groupoids. -/
instance instIsFiberedInGroupoids_lci (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((lci S).ι ⋙ p S) :=
  sorry

/-- A family of curves belongs to the local complete intersection locus
precisely when its structure morphism is a local complete intersection,
equivalently when that morphism is syntomic. -/
theorem classifying_factorsThrough_lci_tfae {S : Scheme.{u}} (P : Obj S) :
    List.TFAE [lci S P, AlgebraicSpace.IsLocalCompleteIntersection (hom P),
      AlgebraicSpace.Syntomic (hom P)] :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a local
complete intersection curve family precisely when it is a local complete
intersection over that field. -/
theorem classifying_factorsThrough_lci_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    lci (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      IsLocalCompleteIntersectionOver k X.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
