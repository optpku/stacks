module

public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroFunctor

/-!
# Derivation-induced square-zero morphisms

A derivation into a finite-dimensional coefficient space defines a residue-compatible
automorphism of its trivial square-zero extension and a morphism from the residue field.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace ArtinianLocalAlgCat

variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Module Λ V] [IsScalarTower Λ k V]

/-- A derivation defines the square-zero endomorphism sending `a + v` to
`a + (v + D a)`. -/
def squareZeroAut (D : Derivation Λ k V) : squareZero Λ k V ⟶ squareZero Λ k V :=
  let coefficientMap : (squareZero Λ k V).carrier → (squareZero Λ k V).carrier :=
    fun x ↦ inl x.fst + inr (x.snd + D x.fst)
  let laws :
      (coefficientMap 1 = 1) ∧
      (∀ x y, coefficientMap (x * y) = coefficientMap x * coefficientMap y) ∧
      (coefficientMap 0 = 0) ∧
      (∀ x y, coefficientMap (x + y) = coefficientMap x + coefficientMap y) ∧
      (∀ base : Λ, coefficientMap (algebraMap Λ _ base) = algebraMap Λ _ base) ∧
      (∀ hom : algebraHom (squareZero Λ k V) (squareZero Λ k V),
        (∀ x, hom x = coefficientMap x) →
          IsLocalHom hom ∧ ∀ localness : IsLocalHom hom,
            residueCompat hom localness = residueIsoHom (squareZero Λ k V)) := sorry
  let hom : (squareZero Λ k V).carrier →ₐ[Λ] (squareZero Λ k V).carrier :=
    { toFun := coefficientMap
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2.1
      commutes' := laws.2.2.2.2.1 }
  let compatibility := laws.2.2.2.2.2 hom (fun _ ↦ rfl)
  Hom.of hom compatibility.1 (compatibility.2 compatibility.1)

/-- The square-zero endomorphism adds the derivation to the infinitesimal coefficient. -/
theorem squareZeroAut_apply (D : Derivation Λ k V) (x : (squareZero Λ k V).carrier) :
    (squareZeroAut D).hom x = inl x.fst + inr (x.snd + D x.fst) := rfl

/-- The morphism associated to a derivation is the canonical inclusion followed by its
square-zero automorphism. -/
def derivationToSquareZero (D : Derivation Λ k V) : residue Λ k ⟶ squareZero Λ k V :=
  residueToSquareZero V ≫ squareZeroAut D

/-- The derivation morphism factors through the canonical inclusion. -/
theorem derivationToSquareZero_eq_comp (D : Derivation Λ k V) :
    derivationToSquareZero D = residueToSquareZero V ≫ squareZeroAut D := rfl

/-- The derivation morphism sends `a` to `inl a + inr (D a)`. -/
theorem derivationToSquareZero_apply (D : Derivation Λ k V) (a : k) :
    (derivationToSquareZero D).hom a = inl a + inr (D a) := sorry

/-- The square-zero automorphism associated to the zero derivation is the identity. -/
theorem squareZeroAut_zero :
    squareZeroAut (0 : Derivation Λ k V) = 𝟙 (squareZero Λ k V) := sorry

/-- Composition of square-zero automorphisms adds their derivations. -/
theorem squareZeroAut_add (D D' : Derivation Λ k V) :
    squareZeroAut D' ≫ squareZeroAut D = squareZeroAut (D + D') := sorry

/-- The square-zero automorphism associated to a derivation has inverse given by its
negative. -/
def squareZeroAutIso (D : Derivation Λ k V) : squareZero Λ k V ≅ squareZero Λ k V :=
  let inverseLaws :
      squareZeroAut D ≫ squareZeroAut (-D) = 𝟙 (squareZero Λ k V) ∧
      squareZeroAut (-D) ≫ squareZeroAut D = 𝟙 (squareZero Λ k V) := sorry
  { hom := squareZeroAut D
    inv := squareZeroAut (-D)
    hom_inv_id := inverseLaws.1
    inv_hom_id := inverseLaws.2 }

/-- The forward map of the derivation-induced isomorphism is its square-zero endomorphism. -/
theorem squareZeroAutIso_hom (D : Derivation Λ k V) :
    (squareZeroAutIso D).hom = squareZeroAut D := rfl

/-- The inverse map of the derivation-induced isomorphism uses the negative derivation. -/
theorem squareZeroAutIso_inv (D : Derivation Λ k V) :
    (squareZeroAutIso D).inv = squareZeroAut (-D) := rfl

end ArtinianLocalAlgCat

end
