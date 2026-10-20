/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion

/-!
# Closed immersions of formal spectra

The continuous homomorphism inducing a closed immersion of formal spectra has dense image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A continuous homomorphism of weakly admissible topological rings over a
scheme has dense image if its induced morphism of formal spectra is a closed immersion. -/
theorem denseRange_of_closedImmersion_spfMap
    {S : Scheme.{u}} {A B : Type u}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    [FormalAlgebraicSpace.ClosedImmersion
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap φ hφ h_over))] :
    DenseRange φ :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
