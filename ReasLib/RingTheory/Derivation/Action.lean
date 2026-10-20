module

public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Restriction action on derivations

Derivations of an algebra act on derivations of a lower algebra by adding their restriction.
-/

@[expose] public section

universe u v w

namespace Derivation

variable {Λ : Type u} {R : Type v} {k : Type w}
  [CommRing Λ] [CommRing R] [CommRing k]
  [Algebra Λ R] [Algebra Λ k] [Algebra R k] [IsScalarTower Λ R k]

/-- Derivations of `k` act on derivations of `R` by translation by their restriction
along the algebra map `R → k`. -/
instance instAddActionOfCompAlgebraMap : AddAction (Derivation Λ k k) (Derivation Λ R k) :=
  AddAction.compHom (Derivation Λ R k) (compAlgebraMapL Λ R k k).toAddMonoidHom

/-- The action of a derivation of `k` adds its restriction to a derivation of `R`. -/
theorem vadd_eq_add_compAlgebraMap (derivation : Derivation Λ k k)
    (baseDerivation : Derivation Λ R k) :
    derivation +ᵥ baseDerivation = baseDerivation + derivation.compAlgebraMap R :=
  add_comm _ _

end Derivation
