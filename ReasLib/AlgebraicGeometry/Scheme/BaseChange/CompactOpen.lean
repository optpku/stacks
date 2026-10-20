/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Sets.Compacts
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Subalgebra

/-!
# Compact-open descent along affine base change

This module records descent of quasi-compact opens through finitely generated subalgebras of an
affine base-change algebra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.AffineBaseChange

/-- A compact open after affine base change descends through a finitely generated subalgebra. -/
theorem exists_fgSubalgebra_compactOpen_preimage_eq
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (V : CompactOpens (Scheme.AffineBaseChange.baseChange k A f).carrier) :
    ∃ (A' : Subalgebra k A) (_ : A'.FG),
      ∃ V' : CompactOpens (Scheme.AffineBaseChange.baseChange k A' f).carrier,
        (Opens.map (Scheme.AffineBaseChange.Subalgebra.map f A').base).obj V'.toOpens =
          V.toOpens := sorry

end AlgebraicGeometry.Scheme.AffineBaseChange
