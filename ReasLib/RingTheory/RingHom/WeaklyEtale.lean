module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly étale ring homomorphisms

This module gives the intrinsic ring-homomorphism form of weak étaleness and records its
locality as a property of commutative ring homomorphisms.
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism is weakly étale when the algebra structure it induces on its codomain
is weakly étale. -/
@[algebraize RingHom.WeaklyEtale.toAlgebra]
def WeaklyEtale (φ : R →+* S) : Prop :=
  @Algebra.WeaklyEtale R S _ _ φ.toAlgebra

namespace WeaklyEtale

/-- The algebra induced by a weakly étale ring homomorphism is weakly étale. -/
theorem toAlgebra {φ : R →+* S} (hφ : φ.WeaklyEtale) :
    @Algebra.WeaklyEtale R S _ _ φ.toAlgebra := sorry

end WeaklyEtale

/-- The algebra map is weakly étale exactly when the corresponding algebra is weakly étale. -/
theorem weaklyEtale_algebraMap [Algebra R S] :
    (algebraMap R S).WeaklyEtale ↔ Algebra.WeaklyEtale R S := sorry

namespace WeaklyEtale

/-- Weak étaleness is local as a property of commutative ring homomorphisms. -/
theorem propertyIsLocal : PropertyIsLocal WeaklyEtale := sorry

end WeaklyEtale

end RingHom
