module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap65.Lemma_65_16_3_Equivalence
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import stacks_project.Chap72.Lemma_72_14_3_GlobalSections
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_26_6_RankLocus

/-!
# Structure-sheaf pushforward along proper flat morphisms

For a proper, flat, finitely presented morphism of algebraic spaces whose
field-valued fibres satisfy `k = Γ(X_k, 𝒪_{X_k})`, the canonical map
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism, remains so after arbitrary base change, and
étale locally `Rf_* 𝒪_X` splits as `𝒪 ⊞ P` with `P` perfect of Tor-amplitude in
`[1, ∞)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The structure sheaf of an algebraic space, placed in degree zero in `D(𝒪_X)`. -/
abbrev structureSheafDerived (X : AlgebraicSpace S) : ModuleDerived X :=
  (DerivedCategory.singleFunctor (Modules X) 0).obj
    (SheafOfModules.unit (structureSheaf X))

/-- `structureSheafDerived X` is the image of `𝒪_X` under the degree-zero single functor. -/
theorem structureSheafDerived_eq (X : AlgebraicSpace S) :
    structureSheafDerived X =
      (DerivedCategory.singleFunctor (Modules X) 0).obj
        (SheafOfModules.unit (structureSheaf X)) :=
  sorry

/-- The derived pushforward `Rf_* 𝒪_X` of the structure sheaf. -/
abbrev pushforwardStructureSheafDerived {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y :=
  (Modules.pushforwardDerived f).obj (structureSheafDerived X)

/-- `pushforwardStructureSheafDerived f` is `Rf_*` applied to `structureSheafDerived X`. -/
theorem pushforwardStructureSheafDerived_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pushforwardStructureSheafDerived f =
      (Modules.pushforwardDerived f).obj (structureSheafDerived X) :=
  sorry

/-- The scheme-theoretic fibre of `f` over a field-valued point, reindexed as an
algebraic space over `Spec(p.K)`. -/
abbrev fiberOverSpec {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    AlgebraicSpace (Spec (.of p.K)) :=
  restrictOver (Over.mk (fiberToSpec f p))

/-- `fiberOverSpec f p` is `restrictOver` of the slice object of `fiberToSpec f p`. -/
theorem fiberOverSpec_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    fiberOverSpec f p = restrictOver (Over.mk (fiberToSpec f p)) :=
  sorry

/-- The hypothesis that every field-valued fibre of `f` satisfies
`k = Γ(X_k, 𝒪_{X_k})`. -/
def fiberGlobalSectionsBijective {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ p : FieldValuedPoint Y, Function.Bijective (globalSectionsMap (fiberOverSpec f p))

/-- Fibrewise global-sections bijectivity unfolds to the field-valued-point quantification. -/
theorem fiberGlobalSectionsBijective_iff {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    fiberGlobalSectionsBijective f ↔
      ∀ p : FieldValuedPoint Y, Function.Bijective (globalSectionsMap (fiberOverSpec f p)) :=
  sorry

namespace Hom

/-- If `f` is proper, flat, and of finite presentation, and every field-valued fibre
satisfies `k = Γ(X_k, 𝒪_{X_k})`, then the canonical map `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism. -/
theorem structureSheafMap_isIso_of_fiberGlobalSections
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (hΓ : fiberGlobalSectionsBijective f) :
    IsIso (structureSheafMap f) :=
  sorry

/-- Under the same hypotheses, the canonical structure-sheaf pushforward map remains an
isomorphism after every base change. -/
theorem baseChange_structureSheafMap_isIso_of_fiberGlobalSections
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (hΓ : fiberGlobalSectionsBijective f) (g : Y' ⟶ Y) :
    IsIso (structureSheafMap (pullback.snd f g)) :=
  sorry

/-- The canonical module map `𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism under the same
fibrewise global-sections hypotheses. -/
theorem unitToPushforward_isIso_of_fiberGlobalSections
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (hΓ : fiberGlobalSectionsBijective f) :
    IsIso (IdealSubobject.unitToPushforward f) :=
  sorry

end Hom

namespace ModuleDerived

/-- Tor-amplitude in `[a, ∞)` on an algebraic space is tested after étale derived
pullback to scheme charts, reducing to `RingedSpace.HasTorAmplitudeGE`. -/
def HasTorAmplitudeGE {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) : Prop :=
  ∀ (U : Over S) (φ : ofOver U ⟶ X) [AlgebraicSpace.Etale φ],
    RingedSpace.HasTorAmplitudeGE
      (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
        ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) a

/-- Lower Tor-amplitude unfolds to the étale-local ringed-space condition on scheme
charts. -/
theorem hasTorAmplitudeGE_iff {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) :
    HasTorAmplitudeGE E a ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [AlgebraicSpace.Etale φ],
        RingedSpace.HasTorAmplitudeGE
          (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
            ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) a :=
  sorry

/-- Étale locally on `Y`, `Rf_* 𝒪_X` is the biproduct of the degree-zero structure
sheaf and a perfect complex of Tor-amplitude in `[1, ∞)`. -/
theorem exists_etale_structureSheafPushforward_decomposition
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (hΓ : fiberGlobalSectionsBijective f) (y : Points Y) :
    ∃ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y) (y' : Points Y'),
      AlgebraicSpace.Etale g ∧ Points.map g y' = y ∧
        ∃ P : ModuleDerived Y',
          IsPerfect P ∧ HasTorAmplitudeGE P 1 ∧
            IsIsomorphic ((pullback g).obj (pushforwardStructureSheafDerived f))
              (structureSheafDerived Y' ⊞ P) :=
  sorry

end ModuleDerived

end AlgebraicGeometry.AlgebraicSpace
