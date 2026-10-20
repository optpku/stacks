module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism
import StacksCheckRecall

/-!
# Morphisms between formal spectra

A morphism of affine formal algebraic spaces `spf B hB ⟶ spf A hA` over `S`
is uniquely of the form `spfMap φ` for a continuous `S`-algebra map
`φ : A →+* B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u

/- Lemma 87.9.10: Let `S` be a scheme. Let `A`, `B` be weakly admissible
topological rings over `S`. Any morphism `f : spf B hB ⟶ spf A hA` of affine
formal algebraic spaces over `S` is equal to `spfMap φ hφ h_over` for a unique
continuous `S`-algebra map `φ : A →+* B`. -/
@[stacks 0AN0] #check (AlgebraicGeometry.AffineFormalAlgebraicSpace.existsUnique_eq_spfMap :
  ∀ {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (f : spf B hB ⟶ spf A hA),
    ∃! φ : A →+* B, ∃ (hφ : Continuous φ)
      (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB),
      f = spfMap φ hφ h_over)
