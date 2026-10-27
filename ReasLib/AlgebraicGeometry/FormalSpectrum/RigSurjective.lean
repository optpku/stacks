/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AlgebraMap.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective

/-!
# A flat finite-type criterion for rig-surjectivity of formal spectra

Faithful flatness of the special fiber and flat finite-type positive truncations
imply rig-surjectivity of the induced map of complete affine formal spectra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicSpace FormalAlgebraicSpace AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- For a complete algebra over a Noetherian complete adic ring, finite type and
flatness of every positive truncation, together with faithful flatness of the
special fiber, imply rig-surjectivity of the induced formal-spectrum morphism. -/
theorem of_finiteType_flat
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (I : Ideal A) [IsAdicComplete I A] [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    (hfinite : ∀ n : ℕ,
      (Ideal.quotientMap ((I ^ (n + 1)).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).FiniteType)
    (hflat : ∀ n : ℕ,
      (Ideal.quotientMap ((I ^ (n + 1)).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).Flat)
    (hff :
      (Ideal.quotientMap (I.map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).FaithfullyFlat)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    RigSurjective (spfAdicCompletionMap B hA I) :=
  sorry

/-- For a complete algebra over a Noetherian complete adic ring with no ideal
torsion, flatness and finite type of every positive truncation make
rig-surjectivity of the induced formal-spectrum morphism equivalent to faithful
flatness of the special fiber. -/
theorem iff_specialFiber_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (I : Ideal A) [IsAdicComplete I A] [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    (h_torsion : I.powerTorsion A 1 = ⊥)
    (hfinite : ∀ n : ℕ,
      (Ideal.quotientMap ((I ^ (n + 1)).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).FiniteType)
    (hflat : ∀ n : ℕ,
      (Ideal.quotientMap ((I ^ (n + 1)).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).Flat)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    RigSurjective (spfAdicCompletionMap B hA I) ↔
      (Ideal.quotientMap (I.map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).FaithfullyFlat :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
