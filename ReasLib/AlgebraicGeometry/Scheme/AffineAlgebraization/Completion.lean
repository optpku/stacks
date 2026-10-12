/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import ReasLib.RingTheory.AdicCompletion.Noetherian

/-!
# Adic completion of an affine algebraization setup

This file records the ring, ideals, affine scheme, and punctured-open morphism obtained by
completing an affine algebraization setup along its distinguished ideal.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The completed ring `A'` associated to an affine algebraization setup. -/
abbrev completionRing (S : AffineAlgebraizationSetup A) : Type u :=
  AdicCompletion S.I A

/-- The extended ideal `I'` in the completed ring. -/
def completionIdeal (S : AffineAlgebraizationSetup A) : Ideal S.completionRing :=
  S.I.map (algebraMap A S.completionRing)

/-- The extended ideal `a'` in the completed ring. -/
def completionClosedIdeal (S : AffineAlgebraizationSetup A) : Ideal S.completionRing :=
  S.a.map (algebraMap A S.completionRing)

/-- The affine scheme `X' = Spec(A')` of the completed ring. -/
abbrev completionSpec (S : AffineAlgebraizationSetup A) : Scheme :=
  Spec (CommRingCat.of S.completionRing)

/-- The morphism `X' ⟶ X` induced by the completion homomorphism `A ⟶ A'`. -/
def completionMap (S : AffineAlgebraizationSetup A) : S.completionSpec ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (algebraMap A S.completionRing))

/-- The punctured open `U'`, represented canonically as the inverse image of `U` in `X'`. -/
def completionOpen (S : AffineAlgebraizationSetup A) : S.completionSpec.Opens :=
  S.completionMap ⁻¹ᵁ S.U

/-- The inverse-image model of `U'` is the complement of the support of `a'`. -/
theorem completionOpen_eq_complement (S : AffineAlgebraizationSetup A) :
    S.completionOpen =
      (Scheme.idealSheafDataOfIdealOnSpec S.completionClosedIdeal).openComplement := sorry

/-- The punctured open in the completed affine scheme is Noetherian. -/
def isNoetherianCompletionOpen (S : AffineAlgebraizationSetup A) :
    IsNoetherian S.completionOpen := sorry

/-- The restriction `U' ⟶ U` of the completion morphism. -/
def completionOpenMap (S : AffineAlgebraizationSetup A) :
    S.completionOpen.toScheme ⟶ S.U.toScheme :=
  S.completionMap ∣_ S.U

/-- The restricted completion morphism commutes with the two open immersions. -/
theorem completionOpenMap_comp_ι (S : AffineAlgebraizationSetup A) :
    S.completionOpenMap ≫ S.U.ι = S.completionOpen.ι ≫ S.completionMap := sorry

/-- The pullback of `I 𝒪_U` to the completed punctured open `U'`. -/
def completionIdealOnOpen (S : AffineAlgebraizationSetup A) :
    S.completionOpen.toScheme.IdealSheafData :=
  ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι).comap S.completionOpenMap

/-- The pulled-back ideal on `U'` is the restriction of the ideal sheaf associated to `I'`. -/
theorem completionIdealOnOpen_eq (S : AffineAlgebraizationSetup A) :
    S.completionIdealOnOpen =
      (Scheme.idealSheafDataOfIdealOnSpec S.completionIdeal).comap S.completionOpen.ι := sorry

/-- The affine completion morphism is flat. -/
def flatCompletionMap (S : AffineAlgebraizationSetup A) :
    Flat S.completionMap := sorry

/-- The completion morphism restricted to `U'` is flat. -/
def flatCompletionOpenMap (S : AffineAlgebraizationSetup A) :
    Flat S.completionOpenMap := sorry

/-- The completed ring is complete along the extended ideal `I'`. -/
def isAdicCompleteCompletionRing (S : AffineAlgebraizationSetup A) :
    IsAdicComplete S.completionIdeal S.completionRing := sorry

/-- The closed subscheme of `U'` cut out by the pulled-back ideal maps isomorphically to the
closed subscheme of `U` cut out by `I 𝒪_U`. -/
def isIsoCompletionOpenSubschemeMap (S : AffineAlgebraizationSetup A) :
    IsIso (Scheme.IdealSheafData.subschemeMap S.completionIdealOnOpen
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) S.completionOpenMap
      (((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι).le_map_comap
        S.completionOpenMap)) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
