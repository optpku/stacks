module

public import ReasLib.FieldTheory.MvRatFunc.Frobenius
public import ReasLib.RingTheory.DualNumber.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Section

/-!
# Derivation sections and a nonsurjective dual-number pullback

Relative derivations give residue-compatible morphisms into dual numbers.
A rational-function partial derivative yields a pullback whose first projection
does not surject onto the residue field.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt
open scoped DualNumber

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The dual-number algebra map associated to a derivation preserves the canonical
residue-field identifications. -/
theorem derivation_residue_compat (D : Derivation Λ k k) :
    residueCompat (A := residue Λ k) (B := dualNumber Λ k)
        D.toDualNumberAlgHom (Derivation.toDualNumberAlgHom_isLocalHom D) =
      residueIsoHom (residue Λ k) := sorry

/-- A relative derivation defines a morphism from the residue-field object to
the dual-number object. -/
def homOfDerivation (D : Derivation Λ k k) : residue Λ k ⟶ dualNumber Λ k :=
  Hom.of D.toDualNumberAlgHom
    (Derivation.toDualNumberAlgHom_isLocalHom D) (derivation_residue_compat D)

/-- The underlying map of the derivation morphism is its dual-number algebra map. -/
theorem homOfDerivation_hom (D : Derivation Λ k k) :
    (homOfDerivation D).hom = D.toDualNumberAlgHom := sorry

/-- The derivation morphism sends `a` to `inl a + inr (D a)`. -/
theorem homOfDerivation_apply (D : Derivation Λ k k) (value : k) :
    (homOfDerivation D).hom value = inl value + inr (D value) := sorry

open MvRatFunc.Frobenius

/-- The first projection of the algebra pullback of the first rational-function
partial-derivative section and the constant section is not surjective. -/
theorem not_surjective_algebraPullback_toResidue (n p : ℕ) [Fact p.Prime] [NeZero n] :
    ¬ Function.Surjective
      (AlgHom.pullbackFst (pderiv n p 0).toDualNumberAlgHom
        (inlAlgHom (baseField n p) (functionField n p) (functionField n p))) := sorry

end ArtinianLocalAlgCat
