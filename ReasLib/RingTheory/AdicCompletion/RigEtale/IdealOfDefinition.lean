/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Rig-étaleness and ideals of definition

For continuous homomorphisms of adic Noetherian rings, rig-étaleness is
independent of the choice of ideal of definition of the source.
-/

@[expose] public section

universe u

open TopologicalRing
open TopologicalRing.Ideal

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The target of a ring homomorphism is rig-étale over `(A, I)` when it is
rig-étale for the algebra structure induced by that homomorphism. -/
def IsRigEtaleOver (φ : A →+* B) (I : Ideal A) : Prop :=
  @Algebra.RigEtale A _ I B _ φ.toAlgebra

/-- Rig-étaleness along a ring homomorphism agrees with algebraic rig-étaleness
for its induced algebra structure. -/
theorem isRigEtaleOver_iff (φ : A →+* B) (I : Ideal A) :
    φ.IsRigEtaleOver I ↔ @Algebra.RigEtale A _ I B _ φ.toAlgebra :=
  Iff.rfl

variable [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
variable [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]

/-- A continuous homomorphism of adic Noetherian rings is adic, topologically
of finite type, and rig-étale for some ideal of definition inducing the target
topology if and only if it is adic, topologically of finite type, and rig-étale
for every ideal of definition of the source. -/
theorem exists_rigEtaleOver_iff_forall {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType ∧
        ∃ I : Ideal A,
          IsIdealOfDefinition I ∧ IsAdic (Ideal.map φ I) ∧ φ.IsRigEtaleOver I) ↔
      (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType ∧
        ∀ I : Ideal A, IsIdealOfDefinition I → φ.IsRigEtaleOver I) :=
  sorry

/-- For an adic continuous homomorphism of adic Noetherian rings that is
topologically of finite type, rig-étaleness for some ideal of definition
inducing the target topology is equivalent to rig-étaleness for every ideal
of definition of the source. -/
theorem isRigEtaleOver_some_iff_forall {φ : A →+* B} (hφ : Continuous φ)
    (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType) :
    (∃ I : Ideal A,
        IsIdealOfDefinition I ∧ IsAdic (Ideal.map φ I) ∧ φ.IsRigEtaleOver I) ↔
      ∀ I : Ideal A, IsIdealOfDefinition I → φ.IsRigEtaleOver I := by
  constructor
  · intro h
    exact ((exists_rigEtaleOver_iff_forall hφ).mp ⟨h_adic, h_tft, h⟩).2.2
  · intro h
    exact ((exists_rigEtaleOver_iff_forall hφ).mpr ⟨h_adic, h_tft, h⟩).2.2

end RingHom
