/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.OverBase
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.BaseIdeal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionMap
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.SpectralSequence.Cohomology
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf.CommAlg
open FilteredComplex.Cohomology.Convergence
open FilteredComplex.RightDerived.SpectralSequence
open RingedSite.Hom.ModuleDerived
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.IdealSheaf
open DerivedCategory

noncomputable section

universe u

namespace SheafOfModules.CommAlg

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

/-- The degree-zero derived object associated to an ordinary `O`-module sheaf. -/
noncomputable abbrev moduleSheafInDegreeZero
    (F₀ : Modules.{u} O) :
    DerivedCategory (Modules.{u} O) :=
  (DerivedCategory.singleFunctor
    (Modules.{u} O) (0 : ℤ)).obj F₀

/-- Derived global sections of an `I O`-complete completion are derived complete over `I`. -/
theorem derivedGlobalSectionsCompletionTarget_isComplete
    (I : Ideal A) (hI : I.FG) (F₀ : Modules.{u} O)
    {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    DerivedCategory.IsDerivedCompleteWithRespectTo
      ((moduleDerivedGlobalSectionsOverBase O).obj Fhat) I := sorry

/-- The canonical comparison from the `I`-adic derived completion of `RΓ_A(F₀)` to
`RΓ_A(Fhat)`, where `Fhat` is an `I O`-adic derived completion of `F₀`. -/
noncomputable def derivedGlobalSectionsCompletionComparison
    (I : Ideal A) (hI : I.FG) (R : DerivedCompletion.Reflector I)
    (F₀ : Modules.{u} O)
    {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    R.obj
        ((moduleDerivedGlobalSectionsOverBase O).obj
          (moduleSheafInDegreeZero F₀)) ⟶
      (moduleDerivedGlobalSectionsOverBase O).obj Fhat :=
  R.lift
    (derivedGlobalSectionsCompletionTarget_isComplete I hI F₀ η hη)
    ((moduleDerivedGlobalSectionsOverBase O).map η)

/-- Derived completion of an ordinary module sheaf commutes with base-valued derived global
sections along a finitely generated ideal. -/
theorem derivedGlobalSectionsCompletionComparisonIsIso
    (I : Ideal A) (hI : I.FG) (R : DerivedCompletion.Reflector I)
    (F₀ : Modules.{u} O)
    {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    IsIso (derivedGlobalSectionsCompletionComparison I hI R F₀ η hη) := sorry

/-- A convergent truncation/right-derived realization of the hypercohomology spectral sequence,
with its canonical target compared to `RΓ_A`. -/
structure ModuleHypercohomologySpectralSequence
    (O : Sheaf J (CommAlgCat.{u} A))
    (Fhat : DerivedCategory (Modules.{u} O)) where
  /-- The canonical truncation-filtration realization for `A`-module-valued global sections. -/
  realization :
    Truncation.Realization (moduleGlobalSectionsOverBase O) Fhat
  /-- The realization converges after its canonical renumbering. -/
  converges : ConvergesViaRenumbering realization.filtered
    realization.originalSequence realization.sequence
  /-- Its abutment is the cohomology of `RΓ_A(Fhat)`. -/
  targetIso : ∀ n : ℤ,
    HomologicalComplex.homology
        (FilteredComplex.underlying realization.filtered) n ≅
      (DerivedCategory.homologyFunctor (_root_.ModuleCat.{u} A) n).obj
        ((moduleDerivedGlobalSectionsOverBase O).obj Fhat)

/-- A truncation realization, convergence, and an abutment comparison determine a
hypercohomology spectral sequence. -/
def ModuleHypercohomologySpectralSequence.ofRealization
    {O : Sheaf J (CommAlgCat.{u} A)}
    {Fhat : DerivedCategory (Modules.{u} O)}
    (realization :
      Truncation.Realization (moduleGlobalSectionsOverBase O) Fhat)
    (converges : ConvergesViaRenumbering realization.filtered
      realization.originalSequence realization.sequence)
    (targetIso : ∀ n : ℤ,
      HomologicalComplex.homology
          (FilteredComplex.underlying realization.filtered) n ≅
        (DerivedCategory.homologyFunctor (_root_.ModuleCat.{u} A) n).obj
          ((moduleDerivedGlobalSectionsOverBase O).obj Fhat)) :
    ModuleHypercohomologySpectralSequence O Fhat :=
  { realization := realization, converges := converges, targetIso := targetIso }

/-- The second page of the hypercohomology spectral sequence consists of right-derived
base-valued global sections of the cohomology sheaves. -/
noncomputable def ModuleHypercohomologySpectralSequence.pageTwoIso
    {Fhat : DerivedCategory (Modules.{u} O)}
    (S : ModuleHypercohomologySpectralSequence O Fhat) (i : ℕ) (j : ℤ) :
    (S.realization.sequence.page 2).X (Int.ofNat i, j) ≅
      ((moduleGlobalSectionsOverBase O).rightDerived i).obj
        ((DerivedCategory.homologyFunctor
          (Modules.{u} O) j).obj Fhat) :=
  S.realization.pageTwoIso i j

/-- The derived completion of an ordinary module sheaf along a finitely generated base ideal
is bounded below. -/
theorem derivedCompletionTarget_isBoundedBelow
    (I : Ideal A) (hI : I.FG) (F₀ : Modules.{u} O)
    {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    DerivedCategory.IsBoundedBelow Fhat := sorry

/-- The derived completion of an ordinary module sheaf along a finitely generated base ideal
admits a convergent hypercohomology spectral sequence. -/
theorem nonemptyCompletedSheafHypercohomologySpectralSequence
    (I : Ideal A) (hI : I.FG) (F₀ : Modules.{u} O)
    {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    Nonempty (ModuleHypercohomologySpectralSequence O Fhat) := sorry

/-- Cohomology of completed derived global sections maps to the abutment of the
completed-sheaf hypercohomology spectral sequence. -/
noncomputable def ModuleHypercohomologySpectralSequence.completionTargetComparison
    (I : Ideal A) (hI : I.FG) (R : DerivedCompletion.Reflector I)
    (F₀ : Modules.{u} O)
    {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η)
    (S : ModuleHypercohomologySpectralSequence O Fhat) (n : ℤ) :
    (DerivedCategory.homologyFunctor (_root_.ModuleCat.{u} A) n).obj
        (R.obj ((moduleDerivedGlobalSectionsOverBase O).obj (moduleSheafInDegreeZero F₀))) ⟶
      HomologicalComplex.homology (FilteredComplex.underlying S.realization.filtered) n :=
  (DerivedCategory.homologyFunctor (_root_.ModuleCat.{u} A) n).map
    (derivedGlobalSectionsCompletionComparison I hI R F₀ η hη) ≫ (S.targetIso n).inv

/-- The common-abutment comparison of the completion and hypercohomology spectral sequences
is invertible. -/
theorem ModuleHypercohomologySpectralSequence.completionTargetComparison_isIso
    (I : Ideal A) (hI : I.FG) (R : DerivedCompletion.Reflector I)
    (F₀ : Modules.{u} O)
    {Fhat : DerivedCategory (Modules.{u} O)}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η)
    (S : ModuleHypercohomologySpectralSequence O Fhat) (n : ℤ) :
    IsIso (S.completionTargetComparison I hI R F₀ η hη n) := sorry

end SheafOfModules.CommAlg
