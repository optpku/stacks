/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Existence
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.EssentiallyFiniteType
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Henselian
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.22.4 (1) -/
@[stacks 0BFR] #check (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_of_field :
  ∀ (k : Type u) [Field k],
    ∃ ω : DerivedCategory (ModuleCat.{u} k), CategoryTheory.DerivedCategory.IsDualizing ω)

/- Lemma 47.22.4 (2) -/
@[stacks 0BFR] #check (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_of_completeLocal :
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A],
    ∃ ω : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing ω)

/- Lemma 47.22.4 (3) -/
@[stacks 0BFR] #check (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_int :
  ∃ ω : DerivedCategory (ModuleCat.{0} ℤ), CategoryTheory.DerivedCategory.IsDualizing ω)

/- Lemma 47.22.4 (4) -/
@[stacks 0BFR] #check (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_of_dedekindDomain :
  ∀ (A : Type u) [CommRing A] [IsDedekindDomain A],
    ∃ ω : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing ω)

/- Lemma 47.22.4 (5) -/
@[stacks 0BFR] #check (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_of_essFiniteType :
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.EssFiniteType A B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (hA : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex HA),
    letI : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
    ∃ η : DerivedCategory (ModuleCat.{u} B), η.IsDualizingComplex HB)

/- Lemma 47.22.4 (6) -/
@[stacks 0BFR] #check (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_of_adicCompletion :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (AdicCompletion I A)))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAhat : MonoidalClosed (DerivedCategory (ModuleCat.{u} (AdicCompletion I A))))
    (hA : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex HA),
    ∃ η : DerivedCategory (ModuleCat.{u} (AdicCompletion I A)),
      η.IsDualizingComplex HAhat)

/- Lemma 47.22.4 (7) -/
@[stacks 0BFR] #check (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_of_henselization :
  ∀ {A Ah : Type u} [CommRing A] [CommRing Ah] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A Ah] [IsHenselizationOf A Ah]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ah))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ah)))
    (hA : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex HA),
    let _ : IsNoetherianRing Ah :=
      IsHenselizationOf.isNoetherianRing (R := A) (S := Ah)
    ∃ η : DerivedCategory (ModuleCat.{u} Ah), η.IsDualizingComplex HAh)

/- Lemma 47.22.4 (8) -/
@[stacks 0BFR] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_of_strictHenselization :
  ∀ {A Ash : Type u} [CommRing A] [CommRing Ash] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} Ash))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HAsh : MonoidalClosed (DerivedCategory (ModuleCat.{u} Ash)))
    (hA : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex HA),
    let _ : IsNoetherianRing Ash :=
      IsStrictHenselizationOf.isNoetherianRing (R := A) (S := Ash)
    ∃ η : DerivedCategory (ModuleCat.{u} Ash), η.IsDualizingComplex HAsh)
