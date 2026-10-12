/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen.BasicOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 40.14.7: for a finite, finitely presented groupoid scheme immersed in
`Spec A`, an ideal whose zero locus is disjoint from the object image and whose union
with that image is closed contains an element `h` such that
`j ⁻¹ᵁ PrimeSpectrum.basicOpen h` is invariant, affine, and contains the prescribed
finite family of points whose orbits consist of generic points. -/
@[stacks 0ABF] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantAffineOpen_preimage_basicOpen :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [AlgebraicGeometry.IsFinite G.s.left] [AlgebraicGeometry.IsFinite G.t.left]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation G.s.left]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation G.t.left]
      {A : CommRingCat.{u}} (j : G.U.left ⟶ AlgebraicGeometry.Spec A)
      [AlgebraicGeometry.IsImmersion j] (I : Ideal A) {m : ℕ}
      (u : Fin m → G.U.left),
      (∀ i, G.t.left '' (G.s.left ⁻¹' {u i}) ⊆ genericPoints G.U.left) →
      Set.range j ∩ PrimeSpectrum.zeroLocus (I : Set A) = ∅ →
      IsClosed (PrimeSpectrum.zeroLocus (I : Set A) ∪ Set.range j) →
      ∃ h : A, h ∈ I ∧
        AlgebraicGeometry.IsAffineOpen (j ⁻¹ᵁ PrimeSpectrum.basicOpen h) ∧
        G.toPreRelation.IsOpenInvariant (j ⁻¹ᵁ PrimeSpectrum.basicOpen h) ∧
        ∀ i, u i ∈ j ⁻¹ᵁ PrimeSpectrum.basicOpen h)
