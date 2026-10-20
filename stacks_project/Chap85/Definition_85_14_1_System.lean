/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Definition_85_14_1_Ringed
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem

/-!
# Simplicial systems in the derived category of modules

A system `(K_n, K_φ)` with `K_n` in `D(O_n)` and transition maps
`K_φ : Lf_φ^* K_m ⟶ K_n` in `D(O_n)`, functorial in simplex operators up to the
canonical derived-pullback comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite (ToposHom)

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

/-- Functoriality of underived module pullbacks along a family of morphisms of ringed topoi
indexed by simplex operators: the identifications `f_{ψ ≫ φ}^* ≅ f_ψ^* ⋙ f_φ^*` and
`f_id^* ≅ 𝟭`. -/
class HasModulePullbackFunctoriality
    (X : SimplexCategory → RingedSite.{u, v, w})
    [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
    (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m))
    [∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint] where
  /-- Canonical identification `f_{ψ ≫ φ}^* ≅ f_ψ^* ⋙ f_φ^*`. -/
  pullbackCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (fHom (ψ ≫ φ)).modulePullback ≅
      (fHom ψ).modulePullback ⋙ (fHom φ).modulePullback
  /-- Canonical identification `f_id^* ≅ 𝟭`. -/
  pullbackIdIso (n : SimplexCategory) :
    (fHom (𝟙 n)).modulePullback ≅
      𝟭 (SheafOfModules.{w} (X n).structureSheaf)

/-- Systems with the canonical comparisons supplied by the legacy interface. -/
abbrev DerivedModuleSystem
    (X : SimplexCategory → RingedSite.{u, v, w})
    [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
    [UnivLE.{max u v, w}]
    (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m))
    [∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.HasModulePullbackDerived (fHom φ)]
    [functoriality : HasModulePullbackFunctoriality X fHom] :=
  RingedSite.Simplicial.DerivedModuleSystem X fHom
    { pullbackCompIso := functoriality.pullbackCompIso
      pullbackIdIso := functoriality.pullbackIdIso }

namespace DerivedModuleSystem

variable {X : SimplexCategory → RingedSite.{u, v, w}}
variable [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable {fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m)}
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fHom φ)]
variable [functoriality : HasModulePullbackFunctoriality X fHom]

/-- Build a derived-module system from degreewise objects, transition maps, and the identity
and composition laws. -/
def of (obj : ∀ n : SimplexCategory, RingedSite.Hom.ModuleDerived.{w} (X n))
    (map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (fHom φ).modulePullbackDerived.obj (obj m) ⟶ obj n)
    (map_id : ∀ n : SimplexCategory,
      (derivedPullbackIdComparisonOf (fHom (𝟙 n)) (functoriality.pullbackIdIso n)).app (obj n) ≫
        map (𝟙 n) = 𝟙 (obj n))
    (map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      (derivedPullbackCompComparisonOf (fHom φ) (fHom ψ) (fHom (ψ ≫ φ))
          (functoriality.pullbackCompIso ψ φ)).app (obj l) ≫
        map (ψ ≫ φ) =
          (fHom φ).modulePullbackDerived.map (map ψ) ≫ map φ) :
    DerivedModuleSystem X fHom :=
  RingedSite.Simplicial.DerivedModuleSystem.of
    { pullbackCompIso := functoriality.pullbackCompIso
      pullbackIdIso := functoriality.pullbackIdIso } obj map map_comp

/-- The transitions of a derived-module system satisfy composition compatibility. -/
theorem spec (K : DerivedModuleSystem X fHom) :
    ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
        (derivedPullbackCompComparisonOf (fHom φ) (fHom ψ) (fHom (ψ ≫ φ))
            (functoriality.pullbackCompIso ψ φ)).app (K.obj l) ≫
          K.map (ψ ≫ φ) =
            (fHom φ).modulePullbackDerived.map (K.map ψ) ≫ K.map φ :=
  K.map_comp

/-- A morphism of derived-module systems is a family of maps in each `D(O_n)` commuting with
the transitions `K_φ`. -/
abbrev Hom (K L : DerivedModuleSystem X fHom) :=
  RingedSite.Simplicial.DerivedModuleSystem.Hom K L

/-- Build a morphism of derived-module systems from stagewise maps satisfying naturality. -/
def homMk {K L : DerivedModuleSystem X fHom}
    (app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ app n =
        (fHom φ).modulePullbackDerived.map (app m) ≫ L.map φ) :
    Hom K L :=
  RingedSite.Simplicial.DerivedModuleSystem.homMk app naturality

/-- The identity morphism of a derived-module system. -/
def Hom.id (K : DerivedModuleSystem X fHom) : Hom K K :=
  RingedSite.Simplicial.DerivedModuleSystem.Hom.id K

/-- Composition of morphisms of derived-module systems. -/
def Hom.comp {K L M : DerivedModuleSystem X fHom}
    (α : Hom K L) (β : Hom L M) : Hom K M :=
  RingedSite.Simplicial.DerivedModuleSystem.Hom.comp α β

/-- Stagewise component of a morphism built by `homMk`. -/
theorem homMk_app {K L : DerivedModuleSystem X fHom}
    (app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ app n =
        (fHom φ).modulePullbackDerived.map (app m) ≫ L.map φ)
    (n : SimplexCategory) :
    (homMk app naturality).app n = app n :=
  rfl

/-- A derived-module system is cartesian when every transition `K_φ` is an isomorphism. -/
class IsCartesian (K : DerivedModuleSystem X fHom) : Prop where
  /-- Every simplex operator acts by an isomorphism in the derived category. -/
  isIso_map : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ)

/-- Cartesianness is equivalent to every transition map being an isomorphism. -/
theorem isCartesian_iff (K : DerivedModuleSystem X fHom) :
    IsCartesian K ↔ ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ) :=
  ⟨fun h ↦ h.isIso_map, fun h ↦ ⟨h⟩⟩

/-- A system whose every transition is an isomorphism is cartesian. -/
def instIsCartesian_of_isIso
    (K : DerivedModuleSystem X fHom)
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ)] :
    IsCartesian K where
  isIso_map := h

end DerivedModuleSystem

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- Case A of Situation 85.3.3: module pullbacks along `ringedToposMap` are functorial in
simplex operators via the canonical underived identifications. -/
instance instHasModulePullbackFunctoriality_ringedToposMap :
    HasModulePullbackFunctoriality
      (fun n ↦ componentRingedSite C J O n) (fun φ ↦ ringedToposMap C J O φ) where
  pullbackCompIso := ringedModulePullbackCompIso C J O
  pullbackIdIso := ringedModulePullbackIdIso C J O

/-- Case A of Situation 85.3.3: derived-module systems on the component ringed sites
`(Sh(C_n), O_n)` with transitions along `ringedToposMap` and the canonical underived
identifications of simplex operators. -/
abbrev DerivedModuleSystemOnComponents :=
  DerivedModuleSystem (fun n ↦ componentRingedSite C J O n)
    (fun φ ↦ ringedToposMap C J O φ)

end CategoryTheory.SimplicialSites
