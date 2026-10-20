/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactHomologyPairing
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Tactic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CompactRepresentation

/-- Chain degree i occupies cochain degree 2-i. This is the usual negative
degree realization followed by shift [-2]; the even shift introduces no sign. -/
def curveDegreeEmbedding : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun i ↦ 2 - (i : ℤ))
    (by intro i j h; dsimp at h; omega)
    (by intro i j; change j + 1 = i ↔ (2 - (i : ℤ)) + 1 = 2 - (j : ℤ); omega)

instance : curveDegreeEmbedding.IsRelIff := by
  unfold curveDegreeEmbedding
  infer_instance

theorem curveDegree_zero : curveDegreeEmbedding.f 0 = 2 := rfl
theorem curveDegree_one : curveDegreeEmbedding.f 1 = 1 := rfl
theorem curveDegree_two : curveDegreeEmbedding.f 2 = 0 := rfl

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Actual zero extension of the closed-coinvariant chain at the source's
curve degrees. The finite input must already carry the actual inverse Tate
twist; no untwisted coefficient is silently identified with it here. -/
def curveHomologyComplex {M : CategoryTheory.Action.ModuleCat.DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) : CochainComplex (CompactModule Λ) ℤ :=
  (coinvariantChain Λ G I).extend curveDegreeEmbedding

/-- Canonical comparison of homology for the explicit degree embedding. -/
def curveHomologyDegreeIso {M : CategoryTheory.Action.ModuleCat.DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) (i : ℕ) :
    (curveHomologyComplex Λ G I).homology (2 - (i : ℤ)) ≅ homology Λ G I i :=
  (coinvariantChain Λ G I).extendHomologyIso curveDegreeEmbedding rfl

end CompactRepresentation
