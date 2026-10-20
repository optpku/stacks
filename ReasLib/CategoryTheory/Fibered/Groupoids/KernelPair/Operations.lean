/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Lift
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Lift
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

/-! # Literal kernel-pair triple operations

The operations in this leaf retain the explicit based pseudo-pullback carriers and
their supplied component maps.  They do not select a map from a bilimit existence
certificate.  The bicategorical law fields may remain deferred in the chapter facade.
-/

@[expose] public section

open CategoryTheory Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u v w

namespace CategoryTheory.FiberedCategoryOver.Groupoids.KernelPair

variable {C : Type u} [Category.{v} C]
variable {X U : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

abbrev kernelPair (f : U ⟶ X) : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C :=
  TwoFibreProduct.apex.{u, v, w, v} f f

abbrev pr0 (f : U ⟶ X) : kernelPair f ⟶ U :=
  TwoFibreProduct.fst.{u, v, w, v} f f

abbrev pr1 (f : U ⟶ X) : kernelPair f ⟶ U :=
  TwoFibreProduct.snd.{u, v, w, v} f f

abbrev tripleProduct (f : U ⟶ X) : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C :=
  TwoFibreProduct.apex.{u, v, w, v}
    (pr1 f ≫ f) f

abbrev composablePairs (f : U ⟶ X) : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C :=
  TwoFibreProduct.apex.{u, v, w, v} (pr1 f) (pr0 f)

abbrev triplePr01 (f : U ⟶ X) : tripleProduct f ⟶ kernelPair f :=
  TwoFibreProduct.fst.{u, v, w, v} (pr1 f ≫ f) f

abbrev triplePr2 (f : U ⟶ X) : tripleProduct f ⟶ U :=
  TwoFibreProduct.snd.{u, v, w, v} (pr1 f ≫ f) f

abbrev pairPr0 (f : U ⟶ X) : composablePairs f ⟶ kernelPair f :=
  TwoFibreProduct.fst.{u, v, w, v} (pr1 f) (pr0 f)

abbrev pairPr1 (f : U ⟶ X) : composablePairs f ⟶ kernelPair f :=
  TwoFibreProduct.snd.{u, v, w, v} (pr1 f) (pr0 f)

def secondFactorCone (f : U ⟶ X) : PseudoPullbackCone f f where
  pt := tripleProduct f
  fst := triplePr01 f ≫ pr1 f
  snd := triplePr2 f
  iso :=
    α_ (triplePr01 f) (pr1 f) f ≪≫
      TwoFibreProduct.comparisonIso.{u, v, w, v} (pr1 f ≫ f) f

def secondFactor (f : U ⟶ X) : tripleProduct f ⟶ kernelPair f :=
  TwoFibreProduct.lift (secondFactorCone f)

def tripleCone (f : U ⟶ X) :
    PseudoPullbackCone (pr1 f) (pr0 f) where
  pt := tripleProduct f
  fst := triplePr01 f
  snd := secondFactor f
  iso := (TwoFibreProduct.lift.fstIso (secondFactorCone f)).symm

def pr02Cone (f : U ⟶ X) : PseudoPullbackCone f f where
  pt := composablePairs f
  fst := pairPr0 f ≫ pr0 f
  snd := pairPr1 f ≫ pr1 f
  iso :=
    α_ (pairPr0 f) (pr0 f) f ≪≫
      whiskerLeftIso (pairPr0 f)
        (TwoFibreProduct.comparisonIso.{u, v, w, v} f f) ≪≫
      (α_ (pairPr0 f) (pr1 f) f).symm ≪≫
      whiskerRightIso
        (TwoFibreProduct.comparisonIso.{u, v, w, v}
          (pr1 f) (pr0 f)) f ≪≫
      α_ (pairPr1 f) (pr0 f) f ≪≫
      whiskerLeftIso (pairPr1 f)
        (TwoFibreProduct.comparisonIso.{u, v, w, v} f f) ≪≫
      (α_ (pairPr1 f) (pr1 f) f).symm

def pr02 (f : U ⟶ X) :
    composablePairs f ⟶ kernelPair f :=
  TwoFibreProduct.lift (pr02Cone f)

def tripleForward (f : U ⟶ X) :
    tripleProduct f ⟶ composablePairs f :=
  TwoFibreProduct.lift (tripleCone f)

def tripleBackwardCone (f : U ⟶ X) :
    PseudoPullbackCone (pr1 f ≫ f) f where
  pt := composablePairs f
  fst := pairPr0 f
  snd := pairPr1 f ≫ pr1 f
  iso :=
    (α_ (pairPr0 f) (pr1 f) f).symm ≪≫
      whiskerRightIso
      (TwoFibreProduct.comparisonIso.{u, v, w, v} (pr1 f) (pr0 f)) f ≪≫
      α_ (pairPr1 f) (pr0 f) f ≪≫
      whiskerLeftIso (pairPr1 f) (TwoFibreProduct.comparisonIso.{u, v, w, v} f f) ≪≫
      (α_ (pairPr1 f) (pr1 f) f).symm

def tripleBackward (f : U ⟶ X) :
    composablePairs f ⟶ tripleProduct f :=
  TwoFibreProduct.lift (tripleBackwardCone f)

/-- Regrouping a triple and returning retains its two stored outer objects.
The comparison uses literal identity component maps. -/
def tripleUnitApp (f : U ⟶ X) (a : (tripleProduct f).total) :
    a ≅ (toFunctor (tripleBackward f)).obj ((toFunctor (tripleForward f)).obj a) :=
  BasedCategory.PseudoPullback.mkIso
    (Iso.refl (BasedCategory.PseudoPullback.baseObj a))
    (Iso.refl (BasedCategory.PseudoPullback.fstObj a))
    (Iso.refl (BasedCategory.PseudoPullback.sndObj a)) sorry sorry sorry

/-- The normalized second pair returns to the original pair by its stored
middle isomorphism and the identity map on its last object. -/
def tripleCounitSecondApp (f : U ⟶ X) (a : (composablePairs f).total) :
    (toFunctor (secondFactor f)).obj ((toFunctor (tripleBackward f)).obj a) ≅
      BasedCategory.PseudoPullback.sndObj a :=
  BasedCategory.PseudoPullback.mkIso
    (BasedCategory.PseudoPullback.sndBaseIso a).symm
    (BasedCategory.PseudoPullback.comparisonIsoApp a)
    (Iso.refl (BasedCategory.PseudoPullback.sndObj
      (BasedCategory.PseudoPullback.sndObj a))) sorry sorry sorry

/-- The counit retains the first pair and uses the original stored middle
isomorphism to identify the second pair. -/
def tripleCounitApp (f : U ⟶ X) (a : (composablePairs f).total) :
    (toFunctor (tripleForward f)).obj ((toFunctor (tripleBackward f)).obj a) ≅ a :=
  BasedCategory.PseudoPullback.mkIso
    (Iso.refl (BasedCategory.PseudoPullback.baseObj a))
    (Iso.refl (BasedCategory.PseudoPullback.fstObj a))
    (tripleCounitSecondApp f a) sorry sorry sorry

def tripleQuasiInverse (f : U ⟶ X) :
    BasedFunctor.QuasiInverse
      (FiberedCategoryOver.Groupoids.toBasedFunctor (tripleForward f)) where
  inverse := FiberedCategoryOver.Groupoids.toBasedFunctor (tripleBackward f)
  unitIso := BasedNatIso.ofComponents (tripleUnitApp f) sorry sorry
  counitIso := BasedNatIso.ofComponents (tripleCounitApp f) sorry sorry

def tripleEquiv (f : U ⟶ X) :
    tripleProduct f ≌ composablePairs f :=
  Bicategory.InducedBicategory.equivalenceMk
    (tripleQuasiInverse f).toEquivalence


end CategoryTheory.FiberedCategoryOver.Groupoids.KernelPair
