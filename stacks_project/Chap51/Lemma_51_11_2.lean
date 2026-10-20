/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalCohomology.FiniteMap
import StacksCheckRecall

@[expose] public section

universe u v w

namespace Module.LocalCohomology

/- Lemma 51.11.2: extending an ideal and a finite module along a finite map from a
universally catenary Noetherian ring preserves the local-cohomology finiteness cutoff. -/
@[stacks 0BJS] #check (Module.LocalCohomology.cutoff_map_eq_of_finite :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [Module.Finite A B] [IsNoetherianRing B] [UniversallyCatenaryRing.{u, v} A]
      (I : Ideal A) (M : Type w) [AddCommGroup M] [Module B M] [Module A M]
      [IsScalarTower A B M] [Module.Finite B M],
      letI : Module.Finite A M := Module.Finite.trans B M
      cutoff (I.map (algebraMap A B)) M = cutoff I M)

end Module.LocalCohomology
