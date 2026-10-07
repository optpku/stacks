module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FlatExtension
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.Henselian.PairHenselization
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Derived extension to the henselization of a Noetherian ring pair preserves dualizing
complexes. -/
theorem pairHenselization
    {A Ah : Type u} [CommRing A] [CommRing Ah] [IsNoetherianRing A]
    (I : Ideal A) [Algebra A Ah] (Ih : Ideal Ah) [IsPairHenselization A I Ah Ih]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ah))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ah)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA) :
    let _ : IsNoetherianRing Ah :=
      IsPairHenselization.isNoetherianRing (B := A) (J := I) (A := Ah) (I := Ih)
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A Ah)).obj ω).IsDualizingComplex HAh := sorry

/-- Derived extension to the adic completion of a Noetherian ring preserves dualizing complexes. -/
theorem adicCompletion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (AdicCompletion I A)))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAhat : MonoidalClosed (DerivedCategory (ModuleCat.{u} (AdicCompletion I A))))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA) :
    ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (AdicCompletion I A))).obj ω).IsDualizingComplex HAhat := sorry

/-- Derived extension to the henselization of a Noetherian local ring preserves dualizing
complexes. -/
theorem henselization
    {A Ah : Type u} [CommRing A] [CommRing Ah] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A Ah] [IsHenselizationOf A Ah]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ah))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ah)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA) :
    let _ : IsNoetherianRing Ah :=
      IsHenselizationOf.isNoetherianRing (R := A) (S := Ah)
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A Ah)).obj ω).IsDualizingComplex HAh := sorry

/-- Derived extension to the strict henselization of a Noetherian local ring preserves dualizing
complexes. -/
theorem strictHenselization
    {A Ash : Type u} [CommRing A] [CommRing Ash] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ash))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAsh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ash)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex HA) :
    let _ : IsNoetherianRing Ash :=
      IsStrictHenselizationOf.isNoetherianRing (R := A) (S := Ash)
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A Ash)).obj ω).IsDualizingComplex HAsh := sorry

/-- Adic completion of a Noetherian ring admitting a dualizing complex again admits a
dualizing complex. -/
theorem exists_of_adicCompletion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (AdicCompletion I A)))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAhat : MonoidalClosed (DerivedCategory (ModuleCat.{u} (AdicCompletion I A))))
    (hA : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex HA) :
    ∃ η : DerivedCategory (ModuleCat.{u} (AdicCompletion I A)),
      η.IsDualizingComplex HAhat := sorry

/-- A henselization of a Noetherian local ring admitting a dualizing complex again admits a
dualizing complex. -/
theorem exists_of_henselization
    {A Ah : Type u} [CommRing A] [CommRing Ah] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A Ah] [IsHenselizationOf A Ah]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ah))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ah)))
    (hA : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex HA) :
    let _ : IsNoetherianRing Ah :=
      IsHenselizationOf.isNoetherianRing (R := A) (S := Ah)
    ∃ η : DerivedCategory (ModuleCat.{u} Ah), η.IsDualizingComplex HAh := sorry

/-- A strict henselization of a Noetherian local ring admitting a dualizing complex again admits
a dualizing complex. -/
theorem exists_of_strictHenselization
    {A Ash : Type u} [CommRing A] [CommRing Ash] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ash))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAsh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ash)))
    (hA : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex HA) :
    let _ : IsNoetherianRing Ash :=
      IsStrictHenselizationOf.isNoetherianRing (R := A) (S := Ash)
    ∃ η : DerivedCategory (ModuleCat.{u} Ash), η.IsDualizingComplex HAsh := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
