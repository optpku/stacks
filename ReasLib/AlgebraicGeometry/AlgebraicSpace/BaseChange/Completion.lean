module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Base change of an algebraic space to the maximal-ideal-adic completion

For a local ring `A`, the spectrum of the `m`-adic completion of `A` is an
algebraic space over `Spec(A)`, and an algebraic space `X` over `Spec(A)` may
be pulled back along this morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism `Spec(A^∧) ⟶ Spec(A)` induced by the maximal-ideal-adic
completion of a local ring `A`. -/
def specAdicCompletionSchemeHom (A : Type u) [CommRing A] [IsLocalRing A] :
    Spec (.of (AdicCompletion (maximalIdeal A) A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))

/-- `specAdicCompletionSchemeHom A` is `Spec.map` of the structure map of the
`m`-adic completion. -/
theorem specAdicCompletionSchemeHom_eq (A : Type u) [CommRing A] [IsLocalRing A] :
    specAdicCompletionSchemeHom A =
      Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) :=
  rfl

/-- The spectrum of the `m`-adic completion of `A`, as an algebraic space over
`Spec(A)`. -/
abbrev specAdicCompletion (A : Type u) [CommRing A] [IsLocalRing A] :
    AlgebraicSpace (Spec (.of A)) :=
  ofOver (Over.mk (specAdicCompletionSchemeHom A))

/-- `specAdicCompletion A` is `ofOver` of `Spec(A^∧)` over `Spec(A)`. -/
theorem specAdicCompletion_eq (A : Type u) [CommRing A] [IsLocalRing A] :
    specAdicCompletion A = ofOver (Over.mk (specAdicCompletionSchemeHom A)) :=
  rfl

/-- The structure morphism `Spec(A^∧) ⟶ Spec(A)` of algebraic spaces over
`Spec(A)`. -/
def specAdicCompletionHom (A : Type u) [CommRing A] [IsLocalRing A] :
    specAdicCompletion A ⟶ ofOver (Over.mk (𝟙 (Spec (.of A)))) :=
  ofOverHomMk (specAdicCompletionSchemeHom A)
    (Category.comp_id (specAdicCompletionSchemeHom A))

/-- `specAdicCompletionHom A` is `ofOverHomMk` of the scheme morphism
`Spec(A^∧) ⟶ Spec(A)`. -/
theorem specAdicCompletionHom_eq (A : Type u) [CommRing A] [IsLocalRing A] :
    specAdicCompletionHom A =
      ofOverHomMk (specAdicCompletionSchemeHom A)
        (Category.comp_id (specAdicCompletionSchemeHom A)) :=
  rfl

/-- The base change `Y = X ×_{Spec(A)} Spec(A^∧)` of an algebraic space over
`Spec(A)` to the spectrum of the `m`-adic completion of `A`. -/
abbrev completionBaseChange (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))) : AlgebraicSpace (Spec (.of A)) :=
  pullback (SchemeRealization.toBase X) (specAdicCompletionHom A)

/-- `completionBaseChange A X` is the fibre product of `SchemeRealization.toBase X` with
`specAdicCompletionHom A`. -/
theorem completionBaseChange_eq (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))) :
    completionBaseChange A X = pullback (SchemeRealization.toBase X) (specAdicCompletionHom A) :=
  rfl

namespace completionBaseChange

/-- The projection `Y ⟶ X` of the base change to the `m`-adic completion. -/
abbrev fst (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))) :
    completionBaseChange A X ⟶ X :=
  pullback.fst (SchemeRealization.toBase X) (specAdicCompletionHom A)

/-- The projection `Y ⟶ Spec(A^∧)` of the base change to the `m`-adic
completion. -/
abbrev snd (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))) :
    completionBaseChange A X ⟶ specAdicCompletion A :=
  pullback.snd (SchemeRealization.toBase X) (specAdicCompletionHom A)

end completionBaseChange

/-- The projections exhibit `completionBaseChange A X` as the fibre product of
`SchemeRealization.toBase X` and `specAdicCompletionHom A`. -/
theorem isPullback_completionBaseChange (A : Type u) [CommRing A] [IsLocalRing A]
    (X : AlgebraicSpace (Spec (.of A))) :
    IsPullback (completionBaseChange.fst A X) (completionBaseChange.snd A X)
      (SchemeRealization.toBase X) (specAdicCompletionHom A) :=
  IsPullback.of_hasPullback (SchemeRealization.toBase X) (specAdicCompletionHom A)

end AlgebraicGeometry.AlgebraicSpace
