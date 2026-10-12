/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.WLocalAffine.FiniteStage
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.WLocalAffine

/- 61.5.2.2 (1): the affine scheme `X_E` is `Spec(A_E)`, the spectrum of the
product of the component localizations indexed by vanishing patterns on `E`. -/
@[stacks 0970] #check (AlgebraicGeometry.Scheme.WLocalAffine.scheme_eq_spec :
  ∀ {A : Type u} [CommRing A] (E : Finset A),
    scheme E = Spec (CommRingCat.of (ring E)))

#check (AlgebraicGeometry.Scheme.WLocalAffine.ring :
  {A : Type u} → [CommRing A] → Finset A → Type u)
#check (AlgebraicGeometry.Scheme.WLocalAffine.scheme :
  {A : Type u} → [CommRing A] → Finset A → Scheme.{u})
#check (AlgebraicGeometry.Scheme.WLocalAffine.instIsAffineScheme :
  ∀ {A : Type u} [CommRing A] (E : Finset A), IsAffine (scheme E))

/- 61.5.2.2 (2): `X_E` is the coproduct of the component spectra
`X_{E', E''} = Spec(A_{Z(E', E'')}^~)`, via the canonical `sigmaIso`. -/
@[stacks 0970] #check (AlgebraicGeometry.Scheme.WLocalAffine.sigmaIso :
  ∀ {A : Type u} [CommRing A] (E : Finset A),
    (∐ fun p : VanishingPattern E ↦ componentScheme p) ≅ scheme E)

#check (AlgebraicGeometry.Scheme.WLocalAffine.componentScheme :
  {A : Type u} → [CommRing A] → {E : Finset A} → VanishingPattern E → Scheme.{u})
#check (AlgebraicGeometry.Scheme.WLocalAffine.ι_comp_sigmaIso :
  ∀ {A : Type u} [CommRing A] (E : Finset A) (p : VanishingPattern E),
    Sigma.ι (fun q : VanishingPattern E ↦ componentScheme q) p ≫ (sigmaIso E).hom =
      Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun q : VanishingPattern E ↦ componentAlgebra q) p)))
