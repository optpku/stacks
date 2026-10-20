module

public import ReasLib.RingTheory.DualNumber.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Residue-compatible dual-number endomorphisms

Derivations of the residue field define local endomorphisms of the dual numbers
that preserve the chosen residue identification.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

/-- A residue-field derivation defines the residue-compatible local dual-number
endomorphism sending `a + vε` to `a + (v + D a)ε`. -/
def dualNumberAut (derivation : Derivation Λ k k) : dualNumber Λ k ⟶ dualNumber Λ k :=
  let laws : IsLocalHom (DualNumber.autOfDerivation derivation) ∧
      ∀ localness : IsLocalHom (DualNumber.autOfDerivation derivation),
        residueCompat (A := dualNumber Λ k) (B := dualNumber Λ k)
          (DualNumber.autOfDerivation derivation) localness =
            residueIsoHom (dualNumber Λ k) := sorry
  Hom.of (DualNumber.autOfDerivation derivation) laws.1 (laws.2 laws.1)

/-- The underlying algebra map of the residue-compatible dual-number endomorphism is
the derivation-induced algebra endomorphism. -/
theorem dualNumberAut_hom (derivation : Derivation Λ k k) :
    (dualNumberAut derivation).hom = DualNumber.autOfDerivation derivation := rfl

/-- A residue-field derivation defines a dual-number automorphism whose inverse is
the automorphism defined by the negative derivation. -/
def dualNumberAutIso (derivation : Derivation Λ k k) : dualNumber Λ k ≅ dualNumber Λ k :=
  let laws :
      (dualNumberAut derivation ≫ dualNumberAut (-derivation) = 𝟙 (dualNumber Λ k)) ∧
      (dualNumberAut (-derivation) ≫ dualNumberAut derivation = 𝟙 (dualNumber Λ k)) := sorry
  { hom := dualNumberAut derivation
    inv := dualNumberAut (-derivation)
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- The forward morphism of the derivation-induced dual-number isomorphism is the
residue-compatible endomorphism defined by that derivation. -/
theorem dualNumberAutIso_hom (derivation : Derivation Λ k k) :
    (dualNumberAutIso derivation).hom = dualNumberAut derivation := rfl

/-- The inverse morphism of the derivation-induced dual-number isomorphism is the
residue-compatible endomorphism defined by the negative derivation. -/
theorem dualNumberAutIso_inv (derivation : Derivation Λ k k) :
    (dualNumberAutIso derivation).inv = dualNumberAut (-derivation) := rfl

/-- The dual-number automorphism defined by the zero derivation is the identity. -/
theorem dualNumberAut_zero :
    dualNumberAut (0 : Derivation Λ k k) = 𝟙 (dualNumber Λ k) := sorry

/-- Composing the dual-number automorphism of one derivation with that of another
gives the automorphism defined by their sum. -/
theorem dualNumberAut_add (derivation derivation' : Derivation Λ k k) :
    dualNumberAut derivation' ≫ dualNumberAut derivation =
      dualNumberAut (derivation + derivation') := sorry

end

end ArtinianLocalAlgCat
