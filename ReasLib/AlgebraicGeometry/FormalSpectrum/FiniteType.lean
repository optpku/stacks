/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Finite type morphisms of formal spectra

A continuous map of weakly admissible topological rings over a scheme induces
a finite type morphism of formal spectra if and only if it is taut and
topologically of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
variable (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
variable [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- The morphism of formal spectra induced by a continuous homomorphism of
weakly admissible topological rings over a scheme is of finite type if and only
if the homomorphism is taut and topologically of finite type. -/
theorem spfMap_finiteType_iff :
    FormalAlgebraicSpace.FiniteType
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
          (spfMap φ hφ h_over)) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
