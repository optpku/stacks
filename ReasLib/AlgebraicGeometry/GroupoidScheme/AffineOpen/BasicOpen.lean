/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Immersion

/-!
# Invariant affine basic opens of groupoid schemes
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- For a finite, finitely presented groupoid scheme immersed in an affine scheme, an ideal
whose zero locus is disjoint from the object image and whose union with that image is closed
contains an element whose basic-open inverse image is affine, invariant, and contains any
prescribed finite family of points whose orbits consist of generic points. -/
theorem exists_invariantAffineOpen_preimage_basicOpen
    {S : Scheme.{u}} (G : GroupoidScheme S) [IsFinite G.s.left] [IsFinite G.t.left]
    [Scheme.Hom.FinitePresentation G.s.left]
    [Scheme.Hom.FinitePresentation G.t.left] {A : CommRingCat.{u}}
    (j : G.U.left ⟶ Spec A) [IsImmersion j] (I : Ideal A) {m : ℕ}
    (u : Fin m → G.U.left)
    (h_orbit : ∀ i, G.t.left '' (G.s.left ⁻¹' {u i}) ⊆ genericPoints G.U.left)
    (h_disjoint : Set.range j ∩ PrimeSpectrum.zeroLocus (I : Set A) = ∅)
    (h_closed : IsClosed (PrimeSpectrum.zeroLocus (I : Set A) ∪ Set.range j)) :
    ∃ h : A, h ∈ I ∧
      IsAffineOpen (j ⁻¹ᵁ PrimeSpectrum.basicOpen h) ∧
      G.toPreRelation.IsOpenInvariant (j ⁻¹ᵁ PrimeSpectrum.basicOpen h) ∧
      ∀ i, u i ∈ j ⁻¹ᵁ PrimeSpectrum.basicOpen h := sorry

end AlgebraicGeometry.GroupoidScheme
