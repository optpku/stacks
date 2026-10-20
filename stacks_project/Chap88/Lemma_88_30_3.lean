/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import stacks_project.Chap88.Lemma_88_30_1_BaseChange

/-!
# Flat local base change of affine 88.30.0.1 categories

A flat local map of local Noetherian rings with `m_B = m_A B` and isomorphic
residue fields induces an equivalence of 88.30.0.1 categories by base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlong
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- Lemma 88.30.3: Let `A → B` be a local map of local Noetherian rings such
that `A → B` is flat, `maximalIdeal B = (maximalIdeal A).map (algebraMap A B)`,
and `κ(maximalIdeal A) ≃ κ(maximalIdeal B)`. Then the base change functor from
the category 88.30.0.1 for `(A, maximalIdeal A)` to the category 88.30.0.1 for
`(B, maximalIdeal B)` is an equivalence. The hypothesis `hmax` identifies the
88.30.1 target closed set `V((maximalIdeal A).map (algebraMap A B))` with
`V(maximalIdeal B)`, so `sourceBaseChangeAlgebraMap B hA (maximalIdeal A)`
lands in the 88.30.0.1 category for `(B, maximalIdeal B)`. The ambient morphism
`hA : Spec (.of A) ⟶ S` recovers the textbook `Spec(A)` as the
identity-over-Spec case. -/
@[stacks 0AF7]
theorem isEquivalence_sourceBaseChangeAlgebraMap_of_flat {A : Type u}
    (B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing A]
    [IsNoetherianRing B] [Module.Flat A B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S)
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hresidue : Function.Bijective (ResidueField.map (algebraMap A B))) :
    (sourceBaseChangeAlgebraMap B hA (maximalIdeal A)).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.completionAlong
