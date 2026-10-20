/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.EtaleCompletion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.FaithfullyFlat
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.Over

/-!
# Surjectivity of completed étale formal-spectrum morphisms

The canonical morphism from the formal spectrum of a completed étale algebra
is surjective exactly when the original algebra is faithfully flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
  (A : Type u) [CommRing A] [Algebra B A]

/-- For an étale algebra over a weakly admissible ring, the canonical morphism
of completed formal spectra is representable with surjective scheme Yoneda
pullbacks if and only if the algebra map is faithfully flat. -/
theorem spfMap_weakIdealCompletion_surjective_iff_faithfullyFlat [Algebra.Etale B A] :
    let f := (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
      (spfMap_weakIdealCompletion hB A)
    (AlgebraicSpace.representableByAlgebraicSpaces f ∧
      ∀ (ha : AlgebraicSpace.representableByAlgebraicSpaces f) ⦃U : Over S⦄
        (ξ : yoneda.obj U ⟶
          (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB)),
        AlgebraicSpace.Surjective (ha.pullbackHom ξ)) ↔
      (algebraMap B A).FaithfullyFlat :=
  sorry

/-- For an étale algebra over a weakly admissible ring, surjectivity of the
canonical completed formal-spectrum morphism, faithful flatness of the algebra
map, and faithful flatness modulo every or some weak ideal of definition are
equivalent. Surjectivity includes representability and is tested on all scheme
Yoneda pullbacks. -/
theorem spfMap_weakIdealCompletion_surjective_tfae [Algebra.Etale B A] :
    let f := (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
      (spfMap_weakIdealCompletion hB A)
    List.TFAE
      [AlgebraicSpace.representableByAlgebraicSpaces f ∧
        ∀ (ha : AlgebraicSpace.representableByAlgebraicSpaces f) ⦃U : Over S⦄
          (ξ : yoneda.obj U ⟶
            (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB)),
          AlgebraicSpace.Surjective (ha.pullbackHom ξ),
        (algebraMap B A).FaithfullyFlat,
        ∀ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J →
          (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat,
        ∃ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J ∧
          (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat] :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
