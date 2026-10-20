/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Rig-smoothness and ideals of definition
-/

@[expose] public section

universe u

open TopologicalRing

namespace RingHom

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]

/-- For a continuous adic homomorphism of adic Noetherian rings that is
topologically of finite type, rig-smoothness is independent of the ideal of
definition of the source. -/
theorem rigSmooth_independentOfIdealOfDefinition {φ : A →+* B}
    (hφ : Continuous φ) (h : φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType)
    {I I' : Ideal A} (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hI' : TopologicalRing.Ideal.IsIdealOfDefinition I') :
    @Algebra.RigSmooth A _ I B _ φ.toAlgebra ↔
      @Algebra.RigSmooth A _ I' B _ φ.toAlgebra :=
  sorry

/-- For a continuous homomorphism of adic Noetherian rings, adicness and
topological finite type together with rig-smoothness for some ideal of
definition inducing the target topology are equivalent to adicness and
topological finite type together with rig-smoothness for every ideal of
definition of the source. -/
theorem exists_rigSmooth_iff_forall_idealOfDefinition {φ : A →+* B}
    (hφ : Continuous φ) :
    ((φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ∧
        ∃ I : Ideal A,
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧
            IsAdic (Ideal.map φ I) ∧
              @Algebra.RigSmooth A _ I B _ φ.toAlgebra) ↔
      ((φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ∧
        ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
          @Algebra.RigSmooth A _ I B _ φ.toAlgebra) :=
  sorry

end RingHom
