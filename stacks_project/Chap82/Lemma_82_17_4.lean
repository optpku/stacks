module

public import Mathlib.RingTheory.Localization.Module
public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
public import stacks_project.Chap71.Lemma_71_10_7
public import stacks_project.Chap71.Lemma_71_10_10
public import stacks_project.Chap82.Definition_82_17_1_Cycle
public import stacks_project.Chap82.Lemma_82_17_4_GmTorsor

/-!
# Lemma 82.17.4

In Situation 82.2.1, for good integral `X / B` and an invertible `𝒪_X`-module
`L`, flat pullback along `q = gmTorsorπ L` identifies `q^* div_L(s)` with the
divisor of the α-transported pullback of a nonzero meromorphic section `s`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open PresheafOfModules SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Objectwise localization of `liftModuleMap φ`, as a morphism of meromorphic-section
presheaves. -/
noncomputable def meromorphicSectionPresheafMap {X : AlgebraicSpace S}
    {F G : X.Modules} (φ : F ⟶ G) :
    meromorphicSectionPresheaf X F ⟶ meromorphicSectionPresheaf X G where
  app U :=
    ModuleCat.ofHom
      { toFun := fun x ↦
          LocalizedModule.map ((regularStructureSections X).obj U)
            ((liftModuleMap φ).val.app U).hom x
        map_add' := sorry
        map_smul' := sorry }
  naturality := sorry

/-- Applying `meromorphicSectionPresheafMap` recovers objectwise `LocalizedModule.map`
of `liftModuleMap`. -/
theorem meromorphicSectionPresheafMap_app {X : AlgebraicSpace S}
    {F G : X.Modules} (φ : F ⟶ G) (U : (smallEtaleSite X)ᵒᵖ)
    (x : meromorphicSectionObj X F U) :
    (meromorphicSectionPresheafMap φ).app U x =
      LocalizedModule.map ((regularStructureSections X).obj U)
        ((liftModuleMap φ).val.app U).hom x :=
  sorry

/-- Sheafification of `meromorphicSectionPresheafMap`, inducing a map `𝒦_X(F) ⟶ 𝒦_X(G)`. -/
noncomputable def meromorphicSectionSheafMap {X : AlgebraicSpace S}
    {F G : X.Modules} (φ : F ⟶ G) :
    meromorphicSectionSheaf X F ⟶ meromorphicSectionSheaf X G :=
  (moduleSheafification (smallEtaleTopology X)
      (regularStructureSections X).localizationPresheaf).map
    (meromorphicSectionPresheafMap φ)

/-- `meromorphicSectionSheafMap` is module-sheafification of
`meromorphicSectionPresheafMap`. -/
theorem meromorphicSectionSheafMap_def {X : AlgebraicSpace S}
    {F G : X.Modules} (φ : F ⟶ G) :
    meromorphicSectionSheafMap φ =
      (moduleSheafification (smallEtaleTopology X)
          (regularStructureSections X).localizationPresheaf).map
        (meromorphicSectionPresheafMap φ) :=
  sorry

/-- The `G_m`-torsor of an invertible module on an integral algebraic space is
integral. -/
instance instIsIntegral_gmTorsor {X : AlgebraicSpace S} (L : X.Modules)
    [isInvertibleObject L] [IsIntegral X] : IsIntegral (gmTorsor L) :=
  sorry

/-- View `q^*(s)` as a meromorphic function on `T` via `α = gmTorsorTriv L`. -/
noncomputable def gmTorsorTrivMeromorphicSection {X : AlgebraicSpace S}
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L) :
    meromorphicSections (gmTorsor L) (𝟙_ (gmTorsor L).Modules) :=
  sectionsMap (meromorphicSectionSheafMap (gmTorsorTriv L).hom)
    (pullbackMeromorphicSections (gmTorsorπ L) L s)

/-- `gmTorsorTrivMeromorphicSection` is sections transport of
`pullbackMeromorphicSections (gmTorsorπ L) L s` along `(gmTorsorTriv L).hom`. -/
theorem gmTorsorTrivMeromorphicSection_def {X : AlgebraicSpace S}
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L) :
    gmTorsorTrivMeromorphicSection L s =
      sectionsMap (meromorphicSectionSheafMap (gmTorsorTriv L).hom)
        (pullbackMeromorphicSections (gmTorsorπ L) L s) :=
  sorry

namespace Hom

export AlgebraicGeometry.AlgebraicSpace (flatPullback)

end Hom

/-- Regularity of a meromorphic section is preserved by pullback along `gmTorsorπ`
and transport along `gmTorsorTriv`. -/
theorem isRegularMeromorphicSection_gmTorsorTriv {X : AlgebraicSpace S}
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) :
    IsRegularMeromorphicSection (gmTorsor L) (𝟙_ (gmTorsor L).Modules)
      (gmTorsorTrivMeromorphicSection L s) :=
  sorry

/-- Lemma 82.17.4: In Situation 82.2.1, for good integral `X / B` and an invertible
`𝒪_X`-module `L`, if `s` is a nonzero meromorphic section of `L` and
`q = gmTorsorπ L : T ⟶ X` is the morphism of Lemma 82.17.3, then
`q^* div_L(s) = div_T(q^*(s))`, where `q^*(s)` is viewed as a nonzero meromorphic
function on `T` via `α = gmTorsorTriv L : q^* L ≅ 𝒪_T`. -/
@[stacks 0EQH]
theorem gmTorsorπ_meromorphicSectionDivisorCycle {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) :
    Hom.flatPullback f (gmTorsorπ L ≫ f) δ (gmTorsorπ L) 1 rfl
        (Hom.deltaDimension f δ (univIrreducibleClosed X) - 1)
        (Hom.meromorphicSectionDivisorCycle f δ s hs) =
      Hom.meromorphicSectionDivisorCycle (gmTorsorπ L ≫ f) δ
        (gmTorsorTrivMeromorphicSection L s)
        (isRegularMeromorphicSection_gmTorsorTriv L s hs) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
