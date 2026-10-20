/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth.IdealOfDefinition
import StacksCheckRecall

/-!
# Independence of the ideal of definition for rig-smooth arrows of WAdm^Noeth
-/

@[expose] public section

universe u

open TopologicalRing

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]

/- Lemma 88.17.1: Let `φ : A →+* B` be a morphism in `WAdm^Noeth`. The
following are equivalent: `φ` satisfies the equivalent conditions of
Lemma 88.11.1 and there exists an ideal of definition of `B` such that `B` is
rig-smooth over `(A, I)`; and `φ` satisfies the equivalent conditions of
Lemma 88.11.1 and for every ideal of definition `I` of `A` the algebra `B` is
rig-smooth over `(A, I)`.

The source's wording with an ideal of definition of `B` is inconsistent with
the pair `(A, I)` and its proof, which require an ideal `I` of `A`. Its mapped
ideal induces the topology on `B`, as expressed by `IsAdic (Ideal.map φ I)`.
The Lemma 88.11.1 conditions are represented by
`φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType`. -/
@[stacks 0GCI] #check (RingHom.exists_rigSmooth_iff_forall_idealOfDefinition :
  ∀ {φ : A →+* B} (hφ : Continuous φ),
    ((φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ∧
        ∃ I : Ideal A,
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧
            IsAdic (Ideal.map φ I) ∧
              @Algebra.RigSmooth A _ I B _ φ.toAlgebra) ↔
      ((φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ∧
        ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
          @Algebra.RigSmooth A _ I B _ φ.toAlgebra))

#check (RingHom.rigSmooth_independentOfIdealOfDefinition :
  ∀ {φ : A →+* B} (hφ : Continuous φ)
    (h : φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType)
    {I I' : Ideal A} (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hI' : TopologicalRing.Ideal.IsIdealOfDefinition I'),
    @Algebra.RigSmooth A _ I B _ φ.toAlgebra ↔
      @Algebra.RigSmooth A _ I' B _ φ.toAlgebra)
