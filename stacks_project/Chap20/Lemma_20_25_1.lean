module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Bounded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Bounded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections

/-! @stack 08BN -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open DerivedCategory.TStructure
open ComplexShape HomologicalComplex₂

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

/- Domain-style sampling for Lemma 20.25.1:
- primary domain: Čech-to-derived-global-sections comparison for bounded-below complexes of
  `𝒪_X`-modules on a ringed space, with the natural target owner level
  `ModuleCat (globalSectionsRing X)`;
- sampled owner declarations:
  `RingedSpace.hasFiniteProducts_over`,
  `moduleGlobalSectionsFunctor`,
  `ModuleCech.Presheaf.complex`,
  `ModuleCech.Presheaf.cohomology`,
  `sectionsRingOnOpen`,
  `moduleSectionsEvaluation_additive`,
  `ObjectProperty.lift`,
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`,
  `DerivedCategory.Plus.Q`,
  `Functor.RightDerived.Bounded.functor`;
- best owner abstraction: the bounded-below comparison should be centered on the
  `Γ(X, 𝒪_X)`-module-valued owners `moduleGlobalSectionsFunctor`,
  `ModuleCech.Presheaf.complex (⊤ : Opens X.carrier)`, and
  `Module.Derived.GlobalSections.Bounded.functor X`; the source-facing comparison should target
  the canonical composite from bounded-below complexes into that owner, with forgetting to
  `AddCommGrpCat` treated only as a bridge/view;
- primitive data: the ringed space `X`, the indexed family of opens `𝒰`, and a bounded-below
  complex `K : CochainComplex.Plus (RingedSpace.Modules X)`;
- derived API: the bounded-below total Čech functor, the bounded-below derived global-sections
  functor, the comparison natural transformation, and the resulting spectral-sequence existence
  theorem.

Source/core/bridge triage:
- `source-facing`: existence of a Čech-to-derived-global-sections comparison with the injective-
  case isomorphism property, and the spectral-sequence existence theorem
  `exists_moduleCechToDerivedGlobalSectionsSpectralSequence`;
- `core/canonical`: `moduleGlobalSectionsFunctor`, `ModuleCech.Presheaf.complex`,
  `ModuleCech.Presheaf.cohomology`, `sectionsRingOnOpen`, `ObjectProperty.lift`,
  `FilteredComplex`,
  `IsAssociatedToFilteredComplex`, `DerivedCategory.Plus.Q`,
  `Functor.RightDerived.Bounded.functor`, and `FilteredComplex.convergesToCohomology`;
- `bridge/view`: forgetting the resulting `Γ(X, 𝒪_X)`-module-valued constructions to
  `AddCommGrpCat`.

This file keeps only the local bounded-below comparison layer; the public owners now stay at the
canonical `Γ(X, 𝒪_X)`-module level, with additive forgetting left to existing bridge
functors. -/

/-- The total Čech complex functor on cochain complexes of `𝒪_X`-modules, valued in
cochain complexes of `Γ(X, 𝒪_X)`-modules, built from the Chapter 20 Čech owner
`ModuleCech.Presheaf.complex`. -/
abbrev moduleCechDoubleFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      HomologicalComplex₂ (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) (up ℤ) :=
  (ModuleCech.extended X 𝒰).mapHomologicalComplex (up ℤ)

/-- The total Čech complex functor on cochain complexes of `𝒪_X`-modules, valued in
cochain complexes of `Γ(X, 𝒪_X)`-modules, built from the Chapter 20 Čech owner
`ModuleCech.Presheaf.complex`. -/
abbrev moduleTotalCechComplexFunctor (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤
      HomologicalComplex (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) :=
  moduleCechDoubleFunctor X 𝒰 ⋙
    (totalFunctor (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) (up ℤ) (up ℤ) :
      HomologicalComplex₂ (ModuleCat.{u} (globalSectionsRing X)) (up ℤ) (up ℤ) ⥤
        HomologicalComplex (ModuleCat.{u} (globalSectionsRing X)) (up ℤ))

-- Proof sketch: the Čech direction is supported in nonnegative degrees, and the input complex is
-- bounded below, so only finitely many summands contribute to sufficiently negative total degrees.
-- Hence the total complex remains bounded below.
/-- The total Čech complex of a bounded-below complex of `𝒪_X`-modules is again bounded
below. -/
theorem moduleTotalCechComplex_obj_mem (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier)
    (K : CochainComplex.Plus (RingedSpace.Modules X)) :
    CochainComplex.plus (ModuleCat.{u} (globalSectionsRing X))
      ((moduleTotalCechComplexFunctor X 𝒰).obj K.obj) := sorry

/-- The canonical bounded-below lift of the total Čech complex functor on
`𝒪_X`-modules, built from the Chapter 20 Čech owner
`ModuleCech.Presheaf.complex`. -/
abbrev moduleTotalCechComplexToPlus (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤
      CochainComplex.Plus (ModuleCat.{u} (globalSectionsRing X)) :=
  (CochainComplex.plus (ModuleCat.{u} (globalSectionsRing X))).lift
    (CochainComplex.Plus.ι (RingedSpace.Modules X) ⋙ moduleTotalCechComplexFunctor X 𝒰)
    (moduleTotalCechComplex_obj_mem X 𝒰)

section DerivedComparison

variable (X)

local notation "ΓModX" => ModuleCat (globalSectionsRing X)
local notation "KplusMod" => CochainComplex.Plus (RingedSpace.Modules X)
local notation "DplusΓX" => DerivedCategory.Plus ΓModX
local notation "HΓX" => DerivedCategory.Plus.homologyFunctor ΓModX
local notation "KplusToDplusModX" =>
  (DerivedCategory.Plus.Q : KplusMod ⥤ DerivedCategory.Plus (RingedSpace.Modules X))
local notation "RΓplus" => Module.Derived.GlobalSections.Bounded.functor X

/-- The bounded-below derived functor represented by total Čech complexes for the family `𝒰`. -/
abbrev moduleCechDerivedFunctor (𝒰 : ι → Opens X.carrier) :
    KplusMod ⥤ DplusΓX :=
  moduleTotalCechComplexToPlus X 𝒰 ⋙ DerivedCategory.Plus.Q

/-- A comparison from bounded-below total Čech complexes to bounded-below derived global sections
has the expected computation property if it becomes an isomorphism on every bounded-below complex
whose terms are injective `𝒪_X`-modules. -/
def IsModuleCechToDerivedGlobalSectionsComparison
    (𝒰 : ι → Opens X.carrier)
    (τ : moduleCechDerivedFunctor X 𝒰 ⟶ KplusToDplusModX ⋙ RΓplus) : Prop :=
  ∀ K : KplusMod,
    (∀ q : ℤ, Injective (K.obj.X q)) → IsIso (τ.app K)

/-- A comparison with the injective-case computation property is an isomorphism on any bounded-
below complex whose terms are injective `𝒪_X`-modules. -/
theorem IsModuleCechToDerivedGlobalSectionsComparison.isIso_app
    {𝒰 : ι → Opens X.carrier}
    {τ : moduleCechDerivedFunctor X 𝒰 ⟶ KplusToDplusModX ⋙ RΓplus}
    (hτ : IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ)
    (K : KplusMod) (hK : ∀ q : ℤ, Injective (K.obj.X q)) :
    IsIso (τ.app K) := sorry

-- Proof sketch: choose a bounded-below injective resolution of the input complex, form the
-- rowwise Čech double complex on that injective resolution, and compare both the total Čech
-- complex and the derived global-sections complex with the total complex of the double complex.
-- Injective sheaf modules are Čech-acyclic on an open cover, so the resulting comparison is a
-- quasi-isomorphism and is natural in the input complex.
/-- Lemma 20.25.1: for an open covering `𝒰 : X = ⋃ i, U_i` of a ringed space `X`, there is a
comparison natural transformation from the total Čech complex functor on bounded-below complexes
of `𝒪_X`-modules to the bounded-below derived global-sections functor `RΓ(X, -)` which is an
isomorphism on bounded-below complexes of injective `𝒪_X`-modules. -/
@[stacks 08BN]
theorem exists_moduleCechToDerivedGlobalSections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤) :
    ∃ τ : moduleCechDerivedFunctor X 𝒰 ⟶ KplusToDplusModX ⋙ RΓplus,
      IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ := sorry

-- Proof sketch: choose a Cartan-Eilenberg resolution of the bounded-below complex `K`, apply the
-- Čech construction rowwise to obtain a triple complex, reinterpret it as a double complex, and
-- then take the second spectral sequence. The `E₂`-page identifies with Čech cohomology of the
-- cohomology sheaves, and convergence follows from the boundedness of the Cartan-Eilenberg model.
/-- A bounded-below Čech-to-hypercohomology spectral sequence for an open cover of a ringed space.
-/
theorem exists_moduleCechToDerivedGlobalSectionsSpectralSequence
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (K : KplusMod) :
    ∃ (filteredComplex : FilteredComplex ΓModX)
      (spectralSequence : CohomologicalSpectralSequence ΓModX 0)
      (associated : FilteredComplex.IsAssociated filteredComplex spectralSequence)
      (pageTwoIso : ∀ p : ℕ, ∀ q : ℤ,
        (spectralSequence.page 2).X (Int.ofNat p, q) ≅
          ModuleCech.Presheaf.cohomology (⊤ : Opens X.carrier)
            (fun i ↦ Over.mk (Opens.leTop (𝒰 i)))
            ((SheafOfModules.forget X.ringCatSheaf).obj (K.obj.homology q)) p)
      (targetIso : ∀ n : ℤ,
        filteredComplex.underlying.homology n ≅
          (HΓX n).obj
            ((RΓplus).obj ((KplusToDplusModX).obj K))),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        FilteredComplex.Cohomology.Filtration.IsFinite filteredComplex ∧
        FilteredComplex.Cohomology.Convergence.Converges
          filteredComplex spectralSequence := sorry

end DerivedComparison

end AlgebraicGeometry.RingedSpace
