/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf.CommAlg
open FilteredComplex.Cohomology.Convergence
open FilteredComplex.RightDerived.SpectralSequence
open SheafOfModules.CommAlg
open RingedSite.Hom.ModuleDerived
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.IdealSheaf
open DerivedCategory

noncomputable section

universe u

variable {A : Type u} {C : Type u}
variable [CommRing A] [SmallCategory C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{u} A) CommRingCat.{u})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J (CommAlgCat.{u} A)}

/- Lemma 52.6.20: derived completion commutes with base-valued derived global sections for
an ordinary module sheaf and a finitely generated ideal. -/
@[stacks 0BLX]
#check (SheafOfModules.CommAlg.derivedGlobalSectionsCompletionComparisonIsIso :
  ∀ (I : Ideal A) (hI : I.FG) (R : DerivedCompletion.Reflector I)
    (F₀ : Modules.{u} O)
    {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u} (ofBaseIdeal O I hI) η),
    IsIso (derivedGlobalSectionsCompletionComparison I hI R F₀ η hη))

variable (I : Ideal A) (hI : I.FG) (F₀ : Modules.{u} O)
variable {Fhat : DerivedCategory (Modules.{u} O)}
variable (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
variable (hη : IsDerivedCompletion.{u, u, u, u} (ofBaseIdeal O I hI) η)

/- Every finitely generated base ideal admits derived-completion reflector data. -/
#check (DerivedCompletion.existsReflector :
  ∀ (I : Ideal A), I.FG → Nonempty (DerivedCompletion.Reflector I))

/- The universal completion lift factors the morphism defining the comparison. -/
#check (DerivedCompletion.Reflector.unit_comp_lift :
  ∀ {I : Ideal A} (R : DerivedCompletion.Reflector I)
    {K L : DerivedCategory (_root_.ModuleCat.{u} A)}
    (hL : DerivedCategory.IsDerivedCompleteWithRespectTo L I) (f : K ⟶ L),
    R.unit.app K ≫ R.lift hL f = f)

/- The first spectral sequence has second page given by the cohomology of completed
cohomology modules and converges to completed derived global sections. -/
#check (DerivedCategory.DerivedCompletion.existsCohomologySpectralSequence I hI
    ((moduleDerivedGlobalSectionsOverBase O).obj (moduleSheafInDegreeZero F₀)) :
  Nonempty (DerivedCategory.DerivedCompletion.CohomologySpectralSequence I
    ((moduleDerivedGlobalSectionsOverBase O).obj (moduleSheafInDegreeZero F₀))))

/- The completed sheaf has a convergent hypercohomology spectral sequence. -/
#check (SheafOfModules.CommAlg.nonemptyCompletedSheafHypercohomologySpectralSequence :
  ∀ (I : Ideal A) (hI : I.FG) (F₀ : Modules.{u} O)
    {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat),
    IsDerivedCompletion.{u, u, u, u} (ofBaseIdeal O I hI) η →
      Nonempty (SheafOfModules.CommAlg.ModuleHypercohomologySpectralSequence O Fhat))

/- The second page consists of right-derived global sections of the cohomology sheaves. -/
#check (SheafOfModules.CommAlg.ModuleHypercohomologySpectralSequence.pageTwoIso :
  ∀ {Fhat : DerivedCategory (Modules.{u} O)}
    (S : SheafOfModules.CommAlg.ModuleHypercohomologySpectralSequence O Fhat) (i : ℕ) (j : ℤ),
    (S.realization.sequence.page 2).X (Int.ofNat i, j) ≅
      ((moduleGlobalSectionsOverBase O).rightDerived i).obj
        ((DerivedCategory.homologyFunctor
          (Modules.{u} O) j).obj Fhat))

/- The first second page consists of cohomology of completed cohomology modules. -/
#check (DerivedCompletion.CohomologySpectralSequence.pageTwoIso :
  ∀ {I : Ideal A} {K : DerivedCategory (_root_.ModuleCat.{u} A)}
    (S : DerivedCompletion.CohomologySpectralSequence I K) (i j : ℤ),
    (S.spectralSequence.page 2).X (i, j) ≅
      S.completion.cohomology i
        ((DerivedCategory.singleFunctor (_root_.ModuleCat.{u} A) (0 : ℤ)).obj
          ((DerivedCategory.homologyFunctor (_root_.ModuleCat.{u} A) j).obj K)))

/- Both spectral sequences retain their convergence specifications. -/
#check (DerivedCompletion.CohomologySpectralSequence.converges :
  ∀ {I : Ideal A} {K : DerivedCategory (_root_.ModuleCat.{u} A)}
    (S : DerivedCompletion.CohomologySpectralSequence I K),
    Converges S.filteredComplex S.spectralSequence)

#check (ModuleHypercohomologySpectralSequence.converges :
  ∀ {O : Sheaf J (CommAlgCat.{u} A)} {Fhat : DerivedCategory (Modules.{u} O)}
    (S : ModuleHypercohomologySpectralSequence O Fhat),
    ConvergesViaRenumbering S.realization.filtered
      S.realization.originalSequence S.realization.sequence)

/- Both abutments compare to cohomology of the same supplied derived completion. -/
#check (DerivedCompletion.CohomologySpectralSequence.canonicalTargetIso :
  ∀ {I : Ideal A} {K : DerivedCategory (_root_.ModuleCat.{u} A)}
    (S : DerivedCompletion.CohomologySpectralSequence I K)
    (R : DerivedCompletion.Reflector I) (n : ℤ),
    S.filteredComplex.underlying.homology n ≅
      (DerivedCategory.homologyFunctor (_root_.ModuleCat.{u} A) n).obj (R.obj K))

#check (ModuleHypercohomologySpectralSequence.completionTargetComparison :
  ∀ (I : Ideal A) (hI : I.FG) (R : DerivedCompletion.Reflector I)
    (F₀ : Modules.{u} O) {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat),
    IsDerivedCompletion.{u, u, u, u} (ofBaseIdeal O I hI) η →
    ∀ (S : ModuleHypercohomologySpectralSequence O Fhat) (n : ℤ),
    (DerivedCategory.homologyFunctor (_root_.ModuleCat.{u} A) n).obj
        (R.obj ((moduleDerivedGlobalSectionsOverBase O).obj (moduleSheafInDegreeZero F₀))) ⟶
      HomologicalComplex.homology (FilteredComplex.underlying S.realization.filtered) n)

#check (ModuleHypercohomologySpectralSequence.completionTargetComparison_isIso :
  ∀ (I : Ideal A) (hI : I.FG) (R : DerivedCompletion.Reflector I)
    (F₀ : Modules.{u} O) {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u} (ofBaseIdeal O I hI) η)
    (S : ModuleHypercohomologySpectralSequence O Fhat) (n : ℤ),
    IsIso (S.completionTargetComparison I hI R F₀ η hη n))
