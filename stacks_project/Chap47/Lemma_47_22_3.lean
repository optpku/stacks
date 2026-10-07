module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Henselian
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.22.3 (1): derived extension to the henselization of a Noetherian
ring pair preserves dualizing complexes. -/
@[stacks 0DWD]
#check (CategoryTheory.DerivedCategory.IsDualizingComplex.pairHenselization :
  ∀ {A Ah : Type u} [CommRing A] [CommRing Ah] [IsNoetherianRing A]
    (I : Ideal A) [Algebra A Ah] (Ih : Ideal Ah)
    [IsPairHenselization A I Ah Ih]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ah))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ah)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA),
    let _ : IsNoetherianRing Ah :=
      IsPairHenselization.isNoetherianRing (B := A) (J := I) (A := Ah) (I := Ih)
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A Ah)).obj ω).IsDualizingComplex HAh)

/- Lemma 47.22.3 (2): derived extension to the adic completion of a
Noetherian ring preserves dualizing complexes. -/
@[stacks 0DWD]
#check (CategoryTheory.DerivedCategory.IsDualizingComplex.adicCompletion :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (AdicCompletion I A)))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAhat : MonoidalClosed (DerivedCategory (ModuleCat.{u} (AdicCompletion I A))))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA),
    ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (AdicCompletion I A))).obj ω).IsDualizingComplex HAhat)

/- Lemma 47.22.3 (3): derived extension to the henselization of a
Noetherian local ring preserves dualizing complexes. -/
@[stacks 0DWD]
#check (CategoryTheory.DerivedCategory.IsDualizingComplex.henselization :
  ∀ {A Ah : Type u} [CommRing A] [CommRing Ah] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A Ah] [IsHenselizationOf A Ah]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ah))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ah)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA),
    let _ : IsNoetherianRing Ah :=
      IsHenselizationOf.isNoetherianRing (R := A) (S := Ah)
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A Ah)).obj ω).IsDualizingComplex HAh)

/- Lemma 47.22.3 (4): derived extension to the strict henselization of a
Noetherian local ring preserves dualizing complexes. -/
@[stacks 0DWD]
#check (CategoryTheory.DerivedCategory.IsDualizingComplex.strictHenselization :
  ∀ {A Ash : Type u} [CommRing A] [CommRing Ash] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ash))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAsh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ash)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA),
    let _ : IsNoetherianRing Ash :=
      IsStrictHenselizationOf.isNoetherianRing (R := A) (S := Ash)
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A Ash)).obj ω).IsDualizingComplex HAsh)

