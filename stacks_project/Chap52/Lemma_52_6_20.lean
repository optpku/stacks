module

public import stacks_project.Chap52.Lemma_52_6_19
public import stacks_project.Chap52.Lemma_52_6_20_GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.SpectralSequence.Cohomology
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.API
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf.CommAlg
open FilteredComplex.Cohomology.Convergence
open FilteredComplex.RightDerived.SpectralSequence
open RingedSite
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.IdealSheaf
open DerivedCategory

noncomputable section

universe u

-- Local instance justification (defeq pin): identifies the derived category used by `singleFunctor` and the spectral-sequence API with `ModuleDerived`.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

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
    (F₀ : SheafOfModules.CommAlg.Modules O) :
    ModuleDerived.{u} (ofCommRingSheaf J (commRing O)) :=
  (DerivedCategory.singleFunctor
    (ModuleCat.{u} (ofCommRingSheaf J (commRing O))) (0 : ℤ)).obj F₀

/-- `moduleSheafInDegreeZero F₀` is the canonical single complex concentrated in degree zero. -/
theorem moduleSheafInDegreeZero_def (F₀ : SheafOfModules.CommAlg.Modules O) :
    moduleSheafInDegreeZero F₀ =
      (DerivedCategory.singleFunctor
        (ModuleCat.{u} (ofCommRingSheaf J (commRing O))) (0 : ℤ)).obj F₀ := sorry

/-- Derived global sections of an `I O`-complete completion are derived complete over `I`. -/
theorem derivedGlobalSectionsCompletionTarget_isComplete
    (I : Ideal A) (hI : I.FG) (F₀ : SheafOfModules.CommAlg.Modules O)
    {Fhat : ModuleDerived.{u} (ofCommRingSheaf J (commRing O))}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    DerivedCategory.IsDerivedCompleteWithRespectTo
      ((moduleDerivedGlobalSectionsOverBase O).obj Fhat) I := sorry

/-- The canonical comparison from the `I`-adic derived completion of `RΓ_A(F₀)` to
`RΓ_A(Fhat)`, where `Fhat` is an `I O`-adic derived completion of `F₀`. -/
noncomputable def derivedGlobalSectionsCompletionComparison
    (I : Ideal A) (hI : I.FG) (F₀ : SheafOfModules.CommAlg.Modules O)
    {Fhat : ModuleDerived.{u} (ofCommRingSheaf J (commRing O))}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    DerivedCategory.derivedCompletionOf I hI
        ((moduleDerivedGlobalSectionsOverBase O).obj
          (moduleSheafInDegreeZero F₀)) ⟶
      (moduleDerivedGlobalSectionsOverBase O).obj Fhat :=
  DerivedCategory.DerivedCompletion.lift I hI
    (derivedGlobalSectionsCompletionTarget_isComplete I hI F₀ η hη)
    ((moduleDerivedGlobalSectionsOverBase O).map η)

/-- The comparison factors the canonical completion map through derived global sections of
the chosen completed sheaf. -/
theorem toDerivedCompletion_comp_derivedGlobalSectionsCompletionComparison
    (I : Ideal A) (hI : I.FG) (F₀ : SheafOfModules.CommAlg.Modules O)
    {Fhat : ModuleDerived.{u} (ofCommRingSheaf J (commRing O))}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    DerivedCategory.toDerivedCompletion I hI
        ((moduleDerivedGlobalSectionsOverBase O).obj
          (moduleSheafInDegreeZero F₀)) ≫
        derivedGlobalSectionsCompletionComparison I hI F₀ η hη =
      (moduleDerivedGlobalSectionsOverBase O).map η := sorry

/-- Lemma 52.6.20 (1): for a finitely generated ideal `I`, the canonical map from the
`I`-adic derived completion of `RΓ_A(F₀)` to `RΓ_A(Fhat)` is an isomorphism. -/
@[stacks 0BLX]
theorem derivedGlobalSectionsCompletionComparisonIsIso
    (I : Ideal A) (hI : I.FG) (F₀ : SheafOfModules.CommAlg.Modules O)
    {Fhat : ModuleDerived.{u} (ofCommRingSheaf J (commRing O))}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    IsIso (derivedGlobalSectionsCompletionComparison I hI F₀ η hη) := sorry

/-- Lemma 52.6.20 (2): completed derived global sections have the canonical cohomology
spectral sequence with second page `H^i(H^j(C, F₀)^∧)` and abutment
`H^(i+j)(RΓ_A(F₀)^∧)`. -/
@[stacks 0BLX]
theorem nonemptyCompletionCohomologySpectralSequence
    (I : Ideal A) (hI : I.FG) (F₀ : SheafOfModules.CommAlg.Modules O) :
    Nonempty
      (DerivedCategory.DerivedCompletion.CohomologySpectralSequence I
        ((moduleDerivedGlobalSectionsOverBase O).obj
          (moduleSheafInDegreeZero F₀))) := sorry

/-- A convergent truncation/right-derived realization of the hypercohomology spectral sequence,
with its canonical target compared to `RΓ_A`. -/
structure CompletedSheafHypercohomologySpectralSequence
    (O : Sheaf J (CommAlgCat.{u} A))
    (Fhat : ModuleDerived.{u} (ofCommRingSheaf J (commRing O))) where
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

/-- Construct the completed-sheaf hypercohomology owner from a canonical realization,
convergence, and the comparison of its abutment with `RΓ_A`. -/
def CompletedSheafHypercohomologySpectralSequence.ofRealization
    {O : Sheaf J (CommAlgCat.{u} A)}
    {Fhat : ModuleDerived.{u} (ofCommRingSheaf J (commRing O))}
    (realization :
      Truncation.Realization (moduleGlobalSectionsOverBase O) Fhat)
    (converges : ConvergesViaRenumbering realization.filtered
      realization.originalSequence realization.sequence)
    (targetIso : ∀ n : ℤ,
      HomologicalComplex.homology
          (FilteredComplex.underlying realization.filtered) n ≅
        (DerivedCategory.homologyFunctor (_root_.ModuleCat.{u} A) n).obj
          ((moduleDerivedGlobalSectionsOverBase O).obj Fhat)) :
    CompletedSheafHypercohomologySpectralSequence O Fhat :=
  { realization := realization, converges := converges, targetIso := targetIso }

/-- Lemma 52.6.20 (3): an `I O`-adically derived-completed module sheaf has the canonical
hypercohomology spectral sequence with second page `H^p(C, H^q(Fhat))`; it converges to
`H^(p+q)(RΓ_A(Fhat))`, hence to the common abutment in clause (1). -/
@[stacks 0BLX]
theorem nonemptyCompletedSheafHypercohomologySpectralSequence
    (I : Ideal A) (hI : I.FG) (F₀ : SheafOfModules.CommAlg.Modules O)
    {Fhat : ModuleDerived.{u} (ofCommRingSheaf J (commRing O))}
    (η : moduleSheafInDegreeZero F₀ ⟶ Fhat)
    (hη : IsDerivedCompletion.{u, u, u, u}
      (ofBaseIdeal O I hI) η) :
    Nonempty (CompletedSheafHypercohomologySpectralSequence O Fhat) := sorry
