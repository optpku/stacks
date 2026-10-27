/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.RigSurjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicSpace FormalAlgebraicSpace AffineFormalAlgebraicSpace

universe u

/- Lemma 88.21.9: Finite type and flatness of all positive truncations of a
complete algebra over a Noetherian complete adic ring, together with faithful
flatness of the special fiber, imply rig-surjectivity of the formal-spectrum map. -/
@[stacks 0AQX] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.of_finiteType_flat :
  ∀ {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B]
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
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S),
    RigSurjective (spfAdicCompletionMap B hA I))
