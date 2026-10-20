module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.RelativeModule

/-!
# Basis-indexed gluing of quasi-coherent modules

This leaf extends basis-indexed scheme gluing data by quasi-coherent modules
and compatible pullback identifications. It owns realization and uniqueness
interfaces for the resulting global pair.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules

/-- Basis-indexed quasi-coherent module data over a basis-indexed scheme gluing datum, with
pullback isomorphisms along inclusions and their cocycle condition. -/
@[stacks 01LI]
structure BasisQuasiCoherentGluing (S : Scheme.{u}) extends Scheme.BasisSchemeGluing.{u, v} S
    where
  /-- The quasi-coherent module on each local scheme. -/
  F : ∀ i : ι, (X i).Modules
  /-- Each local module is quasi-coherent. -/
  isQuasiCoherent : ∀ i : ι, (F i).IsQuasicoherent
  /-- The pullback isomorphism from the module over `X j` to the module over `X i`. -/
  theta : ∀ ⦃i j : ι⦄ (hij : U i ≤ U j), (pullback (rho hij)).obj (F j) ≅ F i
  /-- The transition isomorphisms compose along nested inclusions. -/
  theta_cocycle : ∀ ⦃i j k : ι⦄ (hij : U i ≤ U j) (hjk : U j ≤ U k),
      ((pullbackCongr (cocycle hij hjk)).hom.app (F k)) ≫
          ((pullbackComp (rho hij) (rho hjk)).inv.app (F k)) ≫
            (pullback (rho hij)).map (theta hjk).hom ≫
              (theta hij).hom =
        (theta (hij.trans hjk)).hom

namespace BasisQuasiCoherentGluing

variable {S : Scheme.{u}}
variable (D : BasisQuasiCoherentGluing.{u, v} S)

/-- Extend basis-indexed scheme gluing data by explicitly supplied quasi-coherent modules,
pullback isomorphisms, and their cocycle. -/
def ofBasisSchemeGluing (scheme : Scheme.BasisSchemeGluing.{u, v} S)
    (F : ∀ i : scheme.ι, (scheme.X i).Modules)
    (isQuasiCoherent : ∀ i : scheme.ι, (F i).IsQuasicoherent)
    (theta : ∀ ⦃i j : scheme.ι⦄ (hij : scheme.U i ≤ scheme.U j),
      (pullback (scheme.rho hij)).obj (F j) ≅ F i)
    (theta_cocycle : ∀ ⦃i j k : scheme.ι⦄ (hij : scheme.U i ≤ scheme.U j)
      (hjk : scheme.U j ≤ scheme.U k),
      ((pullbackCongr (scheme.cocycle hij hjk)).hom.app (F k)) ≫
          ((pullbackComp (scheme.rho hij) (scheme.rho hjk)).inv.app (F k)) ≫
            (pullback (scheme.rho hij)).map (theta hjk).hom ≫
              (theta hij).hom =
        (theta (hij.trans hjk)).hom) :
    BasisQuasiCoherentGluing.{u, v} S where
  toBasisSchemeGluing := scheme
  F := F
  isQuasiCoherent := isQuasiCoherent
  theta := theta
  theta_cocycle := theta_cocycle

/-- Reorient a local module isomorphism from pullback coordinates to pullback along the inverse
of the local scheme isomorphism. -/
def reorientedLocalModuleIso {Y : Scheme.{u}} (toBase : Y ⟶ S) (M : Y.Modules)
    (localSchemeIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i)
    (localModuleIso : ∀ i : D.ι,
      (pullback (localSchemeIso i).hom).obj (D.F i) ≅
        M.restrict (toBase ⁻¹ᵁ D.U i).ι)
    (i : D.ι) :
    D.F i ≅ (pullback (localSchemeIso i).inv).obj (M.restrict (toBase ⁻¹ᵁ D.U i).ι) :=
  (((Scheme.Modules.pullbackId (D.X i)).app (D.F i)).symm ≪≫
      ((Scheme.Modules.pullbackCongr (localSchemeIso i).inv_hom_id).app (D.F i)).symm ≪≫
        ((Scheme.Modules.pullbackComp (localSchemeIso i).inv
          (localSchemeIso i).hom).app (D.F i)).symm) ≪≫
    (Scheme.Modules.pullback (localSchemeIso i).inv).mapIso (localModuleIso i)

/-- The canonical source identification in the relative gluing comparison, obtained from the
recorded equality between a local transition and the prescribed transition morphism. -/
def localTransitionSourceIso {Y : Scheme.{u}} (toBase : Y ⟶ S)
    (localSchemeIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i) {i j : D.ι}
    (hij : D.U i ≤ D.U j)
    (localTransition : (localSchemeIso i).inv ≫
        Y.homOfLE (toBase.preimage_mono hij) ≫ (localSchemeIso j).hom = D.rho hij) :
    (pullback (D.rho hij)).obj (D.F j) ≅
      (pullback (localSchemeIso i).inv).obj
        (((pullback (localSchemeIso j).hom).obj (D.F j)).restrict
          (Y.homOfLE (toBase.preimage_mono hij))) :=
  ((pullbackCongr localTransition.symm).app (D.F j)) ≪≫
    ((pullbackComp (localSchemeIso i).inv
      (Y.homOfLE (toBase.preimage_mono hij) ≫ (localSchemeIso j).hom)).app (D.F j)).symm ≪≫
      (pullback (localSchemeIso i).inv).mapIso
        (((pullbackComp (Y.homOfLE (toBase.preimage_mono hij))
          (localSchemeIso j).hom).app (D.F j)).symm) ≪≫
        (pullback (localSchemeIso i).inv).mapIso
          (((restrictFunctorIsoPullback
            (Y.homOfLE (toBase.preimage_mono hij))).app
              ((pullback (localSchemeIso j).hom).obj (D.F j))).symm)

/-- The canonical restriction of a chosen local module isomorphism from a larger basis open to
a nested basis open, expressed in the inverse coordinates of the smaller local scheme. -/
def restrictedLocalModuleIso {Y : Scheme.{u}} (toBase : Y ⟶ S) (M : Y.Modules)
    (localSchemeIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i)
    (localModuleIso : ∀ i : D.ι,
      (pullback (localSchemeIso i).hom).obj (D.F i) ≅
        M.restrict (toBase ⁻¹ᵁ D.U i).ι) {i j : D.ι} (hij : D.U i ≤ D.U j) :
    (pullback (localSchemeIso i).inv).obj
        (((pullback (localSchemeIso j).hom).obj (D.F j)).restrict
          (Y.homOfLE (toBase.preimage_mono hij))) ≅
      (pullback (localSchemeIso i).inv).obj (M.restrict (toBase ⁻¹ᵁ D.U i).ι) :=
  (pullback (localSchemeIso i).inv).mapIso
    ((restrictFunctor (Y.homOfLE (toBase.preimage_mono hij))).mapIso (localModuleIso j) ≪≫
      ((restrictFunctorComp (Y.homOfLE (toBase.preimage_mono hij))
        (toBase ⁻¹ᵁ D.U j).ι).app M).symm ≪≫
      (restrictFunctorCongr
        (Y.homOfLE_ι (toBase.preimage_mono hij))).app M)

/-- For every nested pair of basis opens, the canonical relative gluing comparison equals the
prescribed transition morphism. -/
def LocalModuleCompatibility {Y : Scheme.{u}} (toBase : Y ⟶ S) (M : Y.Modules)
    (localSchemeIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i)
    (localTransition : ∀ ⦃i j : D.ι⦄ (hij : D.U i ≤ D.U j),
      (localSchemeIso i).inv ≫ Y.homOfLE (toBase.preimage_mono hij) ≫
        (localSchemeIso j).hom = D.rho hij)
    (localModuleIso : ∀ i : D.ι,
      (pullback (localSchemeIso i).hom).obj (D.F i) ≅
        M.restrict (toBase ⁻¹ᵁ D.U i).ι) : Prop :=
  ∀ ⦃i j : D.ι⦄ (hij : D.U i ≤ D.U j),
    relativeGlueingComparison toBase (D.rho hij) (D.F j) (D.F i) M
        (localSchemeIso i) hij (localSchemeIso j)
        (localTransitionSourceIso D toBase localSchemeIso hij (localTransition hij))
        (restrictedLocalModuleIso D toBase M localSchemeIso localModuleIso hij).hom
        (reorientedLocalModuleIso D toBase M localSchemeIso localModuleIso i) =
      (D.theta hij).hom

/-- A realization of a basis-indexed quasi-coherent gluing datum is a scheme over `S` with a
quasi-coherent module, local scheme and module identifications, and the required compatibility.
-/
@[stacks 01LI]
structure Realization where
  /-- The glued scheme. -/
  Y : Scheme.{u}
  /-- The structure morphism to `S`. -/
  toBase : Y ⟶ S
  /-- The glued module. -/
  M : Y.Modules
  /-- The glued module is quasi-coherent. -/
  isQuasiCoherent : M.IsQuasicoherent
  /-- The local scheme identification over each basis open. -/
  localSchemeIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i
  /-- The local scheme identification is over its basis open. -/
  localSchemeIso_hom_over :
    ∀ i : D.ι, (localSchemeIso i).hom ≫ D.f i = toBase ∣_ D.U i
  /-- Local scheme identifications recover the transition morphisms. -/
  localTransition : ∀ ⦃i j : D.ι⦄ (hij : D.U i ≤ D.U j),
      (localSchemeIso i).inv ≫
          Y.homOfLE (toBase.preimage_mono hij) ≫
            (localSchemeIso j).hom =
        D.rho hij
  /-- The local module identification in pullback coordinates. -/
  localModuleIso : ∀ i : D.ι,
      (pullback (localSchemeIso i).hom).obj (D.F i) ≅
        M.restrict (toBase ⁻¹ᵁ D.U i).ι
  /-- The local module identifications recover the prescribed transition maps. -/
  localModuleIso_comp :
    LocalModuleCompatibility D toBase M localSchemeIso localTransition localModuleIso

namespace Realization

/-- Forget the global module and its identifications from a quasi-coherent-module realization. -/
def toSchemeRealization (R : Realization D) : D.toBasisSchemeGluing.Realization where
  Y := R.Y
  toBase := R.toBase
  localIso := R.localSchemeIso
  localIso_hom_over := R.localSchemeIso_hom_over
  localTransition := R.localTransition

/-- The local module isomorphism of a realization in inverse-image coordinates. -/
abbrev inverseLocalModuleIso (R : Realization D) (i : D.ι) :
    D.F i ≅ (pullback (R.localSchemeIso i).inv).obj (R.M.restrict (R.toBase ⁻¹ᵁ D.U i).ι) :=
  reorientedLocalModuleIso D R.toBase R.M R.localSchemeIso R.localModuleIso i

end Realization

/-- An isomorphism over `S` between global scheme-module pairs. -/
structure GlobalPairOverIso {X Y : Scheme.{u}} (f : X ⟶ S) (𝓕 : X.Modules) (g : Y ⟶ S)
    (𝓖 : Y.Modules) where
  /-- The underlying scheme isomorphism. -/
  iso : X ≅ Y
  /-- The scheme isomorphism lies over `S`. -/
  comm : iso.hom ≫ g = f
  /-- The corresponding module isomorphism after pullback. -/
  moduleIso : (pullback iso.hom).obj 𝓖 ≅ 𝓕

/-- The local comparison induced by a global module isomorphism and the linked restrictions of
its underlying scheme isomorphism. -/
def inducedLocalModuleComparison (R R' : Realization D)
    (schemeIso : D.toBasisSchemeGluing.RealizationIso
      R.toSchemeRealization R'.toSchemeRealization)
    (moduleIso : (pullback schemeIso.iso.hom).obj R'.M ≅ R.M) (i : D.ι) :
    (pullback (R'.localSchemeIso i).inv).obj
        (R'.M.restrict (R'.toBase ⁻¹ᵁ D.U i).ι) ≅
      (pullback (R.localSchemeIso i).inv).obj
        (R.M.restrict (R.toBase ⁻¹ᵁ D.U i).ι) := by
  dsimp only [Realization.toSchemeRealization] at schemeIso
  let schemeIsoAt : (R.toBase ⁻¹ᵁ D.U i).toScheme ≅
      (R'.toBase ⁻¹ᵁ D.U i).toScheme := by
    exact schemeIso.localIso i
  exact (pullback (R'.localSchemeIso i).inv).mapIso
      ((restrictFunctorIsoPullback (R'.toBase ⁻¹ᵁ D.U i).ι).app R'.M) ≪≫
    ((pullbackComp (R'.localSchemeIso i).inv
      (R'.toBase ⁻¹ᵁ D.U i).ι).app R'.M) ≪≫
    ((pullbackCongr (by
      have schemeIso_localIso_hom_localIso :
          schemeIsoAt.hom ≫ (R'.localSchemeIso i).hom =
            (R.localSchemeIso i).hom := by
        simpa only [schemeIsoAt] using
          schemeIso.localIso_hom_localIso i
      have schemeIso_localIso_hom_ι :
          schemeIsoAt.hom ≫ (R'.toBase ⁻¹ᵁ D.U i).ι =
            (R.toBase ⁻¹ᵁ D.U i).ι ≫ schemeIso.iso.hom := by
        simpa only [schemeIsoAt] using
          schemeIso.localIso_hom_ι i
      have localIso_inv : (R'.localSchemeIso i).inv =
          (R.localSchemeIso i).inv ≫ schemeIsoAt.hom := by
        apply (cancel_mono (R'.localSchemeIso i).hom).1
        rw [Category.assoc]
        rw [schemeIso_localIso_hom_localIso]
        simp
      calc
        (R'.localSchemeIso i).inv ≫ (R'.toBase ⁻¹ᵁ D.U i).ι =
            ((R.localSchemeIso i).inv ≫ schemeIsoAt.hom) ≫
              (R'.toBase ⁻¹ᵁ D.U i).ι := by rw [localIso_inv]
        _ = (R.localSchemeIso i).inv ≫
            (schemeIsoAt.hom ≫ (R'.toBase ⁻¹ᵁ D.U i).ι) := by
          rw [Category.assoc]
        _ = (R.localSchemeIso i).inv ≫
            ((R.toBase ⁻¹ᵁ D.U i).ι ≫ schemeIso.iso.hom) := by
          rw [schemeIso_localIso_hom_ι]
        _ = ((R.localSchemeIso i).inv ≫ (R.toBase ⁻¹ᵁ D.U i).ι) ≫
            schemeIso.iso.hom := by rw [Category.assoc])).app R'.M) ≪≫
    ((pullbackComp
      ((R.localSchemeIso i).inv ≫ (R.toBase ⁻¹ᵁ D.U i).ι)
        schemeIso.iso.hom).app R'.M).symm ≪≫
    (pullback ((R.localSchemeIso i).inv ≫
      (R.toBase ⁻¹ᵁ D.U i).ι)).mapIso moduleIso ≪≫
    ((pullbackComp (R.localSchemeIso i).inv
      (R.toBase ⁻¹ᵁ D.U i).ι).app R.M).symm ≪≫
    (pullback (R.localSchemeIso i).inv).mapIso
      (((restrictFunctorIsoPullback (R.toBase ⁻¹ᵁ D.U i).ι).app R.M).symm)

/-- An isomorphism between equipped realizations whose global module isomorphism restricts to
the prescribed local module identifications. -/
structure RealizationIso (R R' : Realization D) where
  /-- The linked isomorphism between the underlying equipped scheme realizations. -/
  schemeIso : D.toBasisSchemeGluing.RealizationIso
    R.toSchemeRealization R'.toSchemeRealization
  /-- The global module isomorphism after pullback along the global scheme isomorphism. -/
  moduleIso : (pullback schemeIso.iso.hom).obj R'.M ≅ R.M
  /-- The induced local restrictions intertwine the chosen local module identifications. -/
  localModuleIso_hom : ∀ i : D.ι,
    (Realization.inverseLocalModuleIso D R' i) ≪≫
        (inducedLocalModuleComparison D R R' schemeIso moduleIso i) =
      Realization.inverseLocalModuleIso D R i

namespace RealizationIso

/-- Forget local compatibility from a realization isomorphism to obtain an isomorphism of the
underlying global scheme-module pairs over the base. -/
def globalPairOverIso {R R' : Realization D} (e : RealizationIso D R R') :
    GlobalPairOverIso R.toBase R.M R'.toBase R'.M where
  iso := e.schemeIso.iso
  comm := e.schemeIso.hom_over
  moduleIso := e.moduleIso

end RealizationIso

/-- A scheme-module pair over `S` realizes `D` when its restrictions are identified with the
prescribed local schemes and modules, including the relative-module compatibility condition. -/
@[stacks 01LI]
def RealizesWithModule {X : Scheme.{u}} (f : X ⟶ S) (𝓕 : X.Modules) : Prop :=
  𝓕.IsQuasicoherent ∧
    ∃ iScheme : ∀ i : D.ι, (f ⁻¹ᵁ D.U i).toScheme ≅ D.X i,
      (∀ i : D.ι, (iScheme i).hom ≫ D.f i = f ∣_ D.U i) ∧
        ∃ localTransition : ∀ ⦃i j : D.ι⦄ (hij : D.U i ≤ D.U j),
            (iScheme i).inv ≫ X.homOfLE (f.preimage_mono hij) ≫ (iScheme j).hom =
              D.rho hij,
          ∃ iModule : ∀ i : D.ι,
              (pullback (iScheme i).hom).obj (D.F i) ≅
                𝓕.restrict (f ⁻¹ᵁ D.U i).ι,
            LocalModuleCompatibility D f 𝓕 iScheme localTransition iModule

/-- A realization supplies a realization witness for its underlying scheme-module pair. -/
theorem Realization.realizesWithModule (R : D.Realization) :
    D.RealizesWithModule R.toBase R.M := sorry

/-- Every compatible basis-indexed quasi-coherent gluing datum admits an equipped global
realization. -/
@[stacks 01LI]
theorem Realization.nonempty :
    Nonempty D.Realization := sorry

/-- Two chosen realizations have a unique compatible isomorphism intertwining all their local
scheme and module identifications. -/
theorem Realization.existsUniqueIso (R R' : D.Realization) :
    ∃ e : RealizationIso D R R', ∀ e' : RealizationIso D R R', e' = e := sorry

/-- Compatible basis-indexed quasi-coherent gluing data have a realization that is unique up
to a unique compatible isomorphism. -/
theorem existsRealizationUniqueUpToUniqueIso :
    ∃ R : D.Realization, ∀ R' : D.Realization,
      ∃ e : RealizationIso D R R', ∀ e' : RealizationIso D R R', e' = e := by
  rcases Realization.nonempty D with ⟨R⟩
  exact ⟨R, fun R' => Realization.existsUniqueIso D R R'⟩

end BasisQuasiCoherentGluing

end AlgebraicGeometry.Scheme.Modules
