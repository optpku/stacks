/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.Adic.Basic

/-!
# Adic homomorphisms of pre-adic rings

A ring homomorphism of pre-adic rings is adic when some ideal of definition of the source
induces the ambient topology on the target.
-/

@[expose] public section

universe u v w

namespace RingHom

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A]
variable [CommRing B] [TopologicalSpace B]

/-- A homomorphism of pre-adic rings is adic if some ideal of definition of the source
induces the ambient topology on the target. -/
def IsAdicHom [TopologicalRing.IsPreadicRing A] [TopologicalRing.IsPreadicRing B]
    (φ : A →+* B) : Prop :=
  ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧ IsAdic (Ideal.map φ I)

variable [TopologicalRing.IsPreadicRing A] [TopologicalRing.IsPreadicRing B]

namespace IsAdicHom

/-- Exhibit an adic homomorphism by an ideal of definition inducing the target topology. -/
theorem of (φ : A →+* B) (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hmap : IsAdic (Ideal.map φ I)) : φ.IsAdicHom := sorry

/-- An adic homomorphism admits an ideal of definition inducing the target topology. -/
theorem exists_isIdealOfDefinition {φ : A →+* B} (hφ : φ.IsAdicHom) :
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧ IsAdic (Ideal.map φ I) :=
  sorry

/-- An adic homomorphism of pre-adic rings is continuous. -/
theorem continuous {φ : A →+* B} (hφ : φ.IsAdicHom) : Continuous φ := sorry

end IsAdicHom

/-- A homomorphism of pre-adic rings is adic if and only if every ideal of definition of the
source induces the ambient topology on the target. -/
theorem isAdicHom_iff (φ : A →+* B) :
    φ.IsAdicHom ↔
      ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → IsAdic (Ideal.map φ I) :=
  sorry

variable {C : Type w}
variable [CommRing C] [TopologicalSpace C] [TopologicalRing.IsPreadicRing C]

namespace IsAdicHom

/-- The composite of continuous adic homomorphisms is adic. -/
theorem comp {φ : A →+* B} {ψ : B →+* C} (hφ_cont : Continuous φ)
    (hψ_cont : Continuous ψ) (hφ : φ.IsAdicHom) (hψ : ψ.IsAdicHom) :
    (ψ.comp φ).IsAdicHom := sorry

/-- If a composite of continuous homomorphisms is adic, then the second homomorphism is adic. -/
theorem of_comp {φ : A →+* B} {ψ : B →+* C} (hφ_cont : Continuous φ)
    (hψ_cont : Continuous ψ) (h : (ψ.comp φ).IsAdicHom) : ψ.IsAdicHom := sorry

end IsAdicHom

end RingHom
