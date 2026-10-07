module

public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locality of tensor products

This leaf owns the local-algebra criterion for a tensor product in which one
factor is integral and one of the two canonical maps of residue fields is
purely inseparable.  The localness and integrality witnesses are ordinary
arguments, so a consumer can use the API without installing noncanonical
temporary instances.  The residue condition is attached directly to
`IsLocalRing.ResidueField.map`, rather than to an arbitrarily chosen algebra
structure on residue fields.

@stack 092Y
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct.Locality

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]

/-- The residue-field hypothesis used by the tensor-product locality
criterion: at least one of the two canonical residue-field maps is purely
inseparable.  The localness proofs are explicit inputs, so this predicate does
not depend on temporary residue-field instances. -/
@[stacks 092Y "purely inseparable tensor-product residue condition"]
def residueFieldPurelyInseparable
    (hAB : IsLocalHom (algebraMap A B))
    (hAC : IsLocalHom (algebraMap A C)) : Prop :=
  (@IsLocalRing.ResidueField.map A C _ _ _ _ (algebraMap A C) hAC).IsPurelyInseparable ∨
    (@IsLocalRing.ResidueField.map A B _ _ _ _ (algebraMap A B) hAB).IsPurelyInseparable

/-- Lemma 10.156.5, tag `092Y`: if `A → B` and `A → C` are local maps of
local commutative rings, `A → C` is integral, and either canonical residue-field
map `ResidueField A →+* ResidueField C` or `ResidueField A →+* ResidueField B`
is purely inseparable, then `B ⊗[A] C` is local.  The two maps are formed from
the supplied localness proofs, so the statement does not depend on a chosen
residue-field algebra structure. -/
@[stacks 092Y]
theorem isLocalRing
    (hAB : IsLocalHom (algebraMap A B))
    (hAC : IsLocalHom (algebraMap A C))
    (hInt : Algebra.IsIntegral A C)
    (hκ : residueFieldPurelyInseparable hAB hAC) :
    IsLocalRing (B ⊗[A] C) := sorry

/-- Under the hypotheses of `isLocalRing`, the left tensor inclusion is a
local homomorphism.  The localness, integrality, and canonical residue-map
conditions remain explicit input rather than temporary instances. -/
@[stacks 092Y "locality of the left tensor inclusion"]
theorem includeLeft_isLocalHom
    (hAB : IsLocalHom (algebraMap A B))
    (hAC : IsLocalHom (algebraMap A C))
    (hInt : Algebra.IsIntegral A C)
    (hκ : residueFieldPurelyInseparable hAB hAC) :
    IsLocalHom
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C) := sorry

/-- Under the hypotheses of `isLocalRing`, the right tensor inclusion is a
local homomorphism.  The result is phrased with the same explicit canonical
residue-map condition as the locality criterion. -/
@[stacks 092Y "locality of the right tensor inclusion"]
theorem includeRight_isLocalHom
    (hAB : IsLocalHom (algebraMap A B))
    (hAC : IsLocalHom (algebraMap A C))
    (hInt : Algebra.IsIntegral A C)
    (hκ : residueFieldPurelyInseparable hAB hAC) :
    IsLocalHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) := sorry

end Algebra.TensorProduct.Locality

namespace Algebra.TensorProduct.Locality

variable {A : Type u} {B : Type v} {C : Type w}
variable [Field A] [CommRing B] [Field C]
variable [Algebra A B] [Algebra A C] [IsLocalRing B]

/-- For a purely inseparable extension of fields `A → C`, the canonical residue-field map on the
right factor supplies the residue condition for tensor-product locality.  This companion hides
only the canonical identifications `ResidueField A ≃ A` and `ResidueField C ≃ C`; the two local-map
proofs remain explicit so callers do not install temporary `IsLocalHom` instances. -/
@[stacks 092Y "field-extension residue condition for tensor-product locality"]
theorem residueFieldPurelyInseparable_of_field_right
    [IsPurelyInseparable A C]
    (hAB : IsLocalHom (algebraMap A B))
    (hAC : IsLocalHom (algebraMap A C)) :
    residueFieldPurelyInseparable hAB hAC := sorry

end Algebra.TensorProduct.Locality
