/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.Topology.KrullDimension.Equidimensional

/-!
# Smooth families of curves

Smoothness and smoothness of relative dimension one are represented by opens
of the base of a curve family under arbitrary scheme base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves with smooth structure morphism. -/
def smooth (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Smooth (hom P)

/-- Membership in `smooth` is smoothness of the structure morphism. -/
theorem smooth_iff {S : Scheme.{u}} (P : Obj S) :
    smooth S P ↔ AlgebraicSpace.Smooth (hom P) := Iff.rfl

/-- Smoothness of families of curves is invariant under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smooth (S : Scheme.{u}) :
    (smooth S).IsClosedUnderIsomorphisms :=
  sorry

/-- The object property of families of curves whose structure morphism is
smooth of relative dimension one. -/
def smoothDim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1

/-- Membership in `smoothDim1` is smoothness and exact relative dimension one
of the structure morphism. -/
theorem smoothDim1_iff {S : Scheme.{u}} (P : Obj S) :
    smoothDim1 S P ↔
      AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 := Iff.rfl

/-- Smoothness of relative dimension one for families of curves is invariant
under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smoothDim1 (S : Scheme.{u}) :
    (smoothDim1 S).IsClosedUnderIsomorphisms :=
  sorry

/-- A smooth family of curves of relative dimension one is smooth. -/
theorem smoothDim1_le_smooth {S : Scheme.{u}} (P : Obj S) :
    smoothDim1 S P → smooth S P := fun h => h.1

/-- For every family of curves, an open of its base represents smoothness of
its pullback under every scheme base change. -/
theorem exists_smooth_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
      AlgebraicSpace.Smooth
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) ↔
        Set.range T.hom ⊆ U :=
  sorry

/-- For every family of curves, an open of its base represents smoothness of
relative dimension one of its pullback under every scheme base change. -/
theorem exists_smoothDim1_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
      (AlgebraicSpace.Smooth
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) ∧
        RelativeDimension
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) 1) ↔
        Set.range T.hom ⊆ U :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a smooth
curve family precisely when its structure morphism is smooth. -/
theorem classifying_factorsThrough_smooth_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    smooth (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a smooth
curve family of relative dimension one precisely when it is smooth and every
irreducible component has dimension one. -/
theorem smoothDim1_iff_scheme_components
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    smoothDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom ∧
        ∀ Z : irreducibleComponents X.left, topologicalKrullDim Z = 1 :=
  sorry

/-- A nonempty proper scheme of dimension at most one over a field defines a
smooth curve family of relative dimension one precisely when it is smooth and
equidimensional of dimension one. -/
theorem classifying_factorsThrough_smoothDim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1) :
    smoothDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom ∧
        TopologicalSpace.EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
