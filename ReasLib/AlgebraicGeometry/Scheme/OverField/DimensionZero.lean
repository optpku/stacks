/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Artinian.Decomposition
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Coproduct

/-!
# Zero-dimensional schemes over a field

This file records the coproduct presentation of a zero-dimensional locally
algebraic scheme and the affine and finite consequences in the algebraic case.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- Explicit data presenting a scheme over a field as a coproduct of spectra of
finite-dimensional local Artinian algebras over that field. -/
structure FiniteLocalArtinianCoproduct (X : SchemeOverField k) where
  /-- The indexing type for the components. -/
  ι : Type u
  /-- The commutative algebra over the base field attached to each component. -/
  algebra : ι → CommAlgOverField k
  /-- Each component algebra is local. -/
  isLocalRing : ∀ i, IsLocalRing (algebra i)
  /-- Each component algebra is Artinian. -/
  isArtinianRing : ∀ i, IsArtinianRing (algebra i)
  /-- Each component algebra is finite-dimensional over the base field. -/
  finiteDimensional : ∀ i, FiniteDimensional k (algebra i)
  /-- The given scheme is isomorphic over the base field to the coproduct of the
  component spectra. -/
  iso : X ≅ sigmaSpec ι algebra

/-- The canonical morphism from the coproduct of the component spectra to the base
spectrum. -/
def FiniteLocalArtinianCoproduct.toSpec {X : SchemeOverField k}
    (D : FiniteLocalArtinianCoproduct X) :
    (∐ fun i : D.ι ↦ Spec (CommRingCat.of (D.algebra i))) ⟶
      Spec (CommRingCat.of k) :=
  (sigmaSpec D.ι D.algebra).hom

/-- A finite local-Artinian coproduct presentation exposes the local, Artinian,
finite-dimensional, and over-base isomorphism conditions on all its components. -/
theorem FiniteLocalArtinianCoproduct.spec {X : SchemeOverField k}
    (D : FiniteLocalArtinianCoproduct X) :
    (∀ i : D.ι, IsLocalRing (D.algebra i)) ∧
      (∀ i : D.ι, IsArtinianRing (D.algebra i)) ∧
      (∀ i : D.ι, FiniteDimensional k (D.algebra i)) ∧
      Nonempty (X ≅ Over.mk D.toSpec) := sorry

/-- A locally algebraic scheme of topological Krull dimension zero over a field
admits a coproduct presentation by spectra of finite-dimensional local Artinian
algebras over that field. -/
theorem FiniteLocalArtinianCoproduct.exists_of_locallyAlgebraic_of_dimZero
    (X : SchemeOverField k) [LocallyAlgebraic X]
    (hX : topologicalKrullDim X.left = 0) :
    Nonempty (FiniteLocalArtinianCoproduct X) := sorry

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.Algebraic

variable {k : Type u} [Field k]

/-- A zero-dimensional algebraic scheme over a field is affine. -/
theorem isAffine_of_dimZero (X : SchemeOverField k) [Algebraic X]
    (hX : topologicalKrullDim X.left = 0) :
    IsAffine X.left := sorry

/-- The structure morphism of a zero-dimensional algebraic scheme over a field is
finite. -/
theorem isFinite_of_dimZero (X : SchemeOverField k) [Algebraic X]
    (hX : topologicalKrullDim X.left = 0) :
    IsFinite X.hom := sorry

end AlgebraicGeometry.Algebraic
