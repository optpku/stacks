/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Preadditive.Basic
public import ReasLib.CategoryTheory.Functor.OfSequence.Colimit
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_13_4_Product

/-!
# Ideal-power Hom colimits and restriction on algebraic spaces

This file constructs the canonical comparison from the colimit of morphisms out of
ideal-power products of a module sheaf to morphisms between the restrictions to the
open complement of the closed subspace cut out by the ideal.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The additive group of module morphisms from `I^n G` to `F`. -/
noncomputable def idealPowerProductHomStage
    (I : IdealSubobject X) (G F : X.Modules) (n : ℕ) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of ((idealPowerProductSubobject I G n : X.Modules) ⟶ F)

/-- Precomposition with `I^(n+1) G ⟶ I^n G` gives the transition between Hom stages. -/
noncomputable def idealPowerProductHomTransition {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (G F : X.Modules) (n : ℕ) :
    idealPowerProductHomStage I G F n ⟶
      idealPowerProductHomStage I G F (n + 1) :=
  AddCommGrpCat.ofHom
    (Preadditive.leftComp F
      (Subobject.ofLE
        (idealPowerProductSubobject I G (n + 1))
        (idealPowerProductSubobject I G n)
        (IdealPowerProduct.antitone I G n)))

/-- The sequential additive-group diagram `n ↦ Hom(I^n G, F)`. -/
noncomputable def idealPowerProductHomDiagram {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (G F : X.Modules) : ℕ ⥤ AddCommGrpCat.{u + 1} :=
  Functor.ofSequence (idealPowerProductHomTransition I G F)

/-- Restriction of the structure module along an étale morphism is a monomorphism onto
the structure module of the source. -/
instance restrictFunctorObjUnit_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    Mono (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f)) :=
  sorry

/-- Restriction of the structure module along an étale morphism is an epimorphism onto
the structure module of the source. -/
instance restrictFunctorObjUnit_epi {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    Epi (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f)) :=
  sorry

/-- The comparison `𝒪_X ⟶ (restrictFunctor f).obj 𝒪_Y` is an isomorphism. -/
noncomputable instance restrictFunctorObjUnit_isIso {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f)) :=
  isIso_of_mono_of_epi
    (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f))

/-- Identification of the restricted structure module with the structure module of the
source. -/
noncomputable def restrictFunctorObjUnitIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    (restrictFunctor f).obj (SheafOfModules.unit (structureSheaf Y)) ≅
      SheafOfModules.unit (structureSheaf X) :=
  (asIso (SheafOfModules.unitToPushforwardObjUnit (restrictStructureMap f))).symm

/-- A morphism `I^n G ⟶ F` restricts canonically to a morphism `G|_U ⟶ F|_U` on the
complement `U` of the closed subspace cut out by `I`. -/
noncomputable def idealPowerProductHomToRestrictionStageMap {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (G F : X.Modules) (n : ℕ) :
    idealPowerProductHomStage I G F n ⟶
      AddCommGrpCat.of
        ((restrictFunctor (idealOpenComplementι I)).obj G ⟶
          (restrictFunctor (idealOpenComplementι I)).obj F) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ ↦
        inv ((restrictFunctor (idealOpenComplementι I)).map
            (idealPowerProductSubobject I G n).arrow) ≫
          (restrictFunctor (idealOpenComplementι I)).map φ
      map_zero' := sorry
      map_add' := sorry }

/-- Restriction to the complement is compatible with the successor transition on
ideal-power Hom stages. -/
theorem idealPowerProductHomToRestrictionStageMap_naturality {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (G F : X.Modules) (n : ℕ) :
    idealPowerProductHomTransition I G F n ≫
        idealPowerProductHomToRestrictionStageMap I G F (n + 1) =
      idealPowerProductHomToRestrictionStageMap I G F n :=
  sorry

/-- The canonical additive comparison from `colim_n Hom(I^n G, F)` to
`Hom(G|_U, F|_U)` on the complement `U` of the closed subspace cut out by `I`. -/
noncomputable def idealPowerProductHomColimitToRestriction {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (G F : X.Modules) :
    colimit (idealPowerProductHomDiagram I G F) ⟶
      AddCommGrpCat.of
        ((restrictFunctor (idealOpenComplementι I)).obj G ⟶
          (restrictFunctor (idealOpenComplementι I)).obj F) :=
  Functor.ofSequence.colimitDesc
    (idealPowerProductHomTransition I G F)
    (idealPowerProductHomToRestrictionStageMap I G F)
    (idealPowerProductHomToRestrictionStageMap_naturality I G F)

/-- The colimit comparison restricts to its defining restriction map on every Hom stage. -/
@[reassoc]
theorem idealPowerProductHomColimitToRestriction_ι {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (G F : X.Modules) (n : ℕ) :
    colimit.ι (idealPowerProductHomDiagram I G F) n ≫
        idealPowerProductHomColimitToRestriction I G F =
      idealPowerProductHomToRestrictionStageMap I G F n :=
  sorry

/-- For a coherent module `G` on a Noetherian algebraic space and a quasi-coherent
module `F`, the canonical ideal-power Hom comparison to the complement is an
isomorphism. -/
noncomputable instance idealPowerProductHomColimitToRestriction_isIso {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (G F : X.Modules) [G.IsCoherent] [F.IsQuasicoherent] :
    IsIso (idealPowerProductHomColimitToRestriction I G F) :=
  sorry

/-- The sequential diagram `n ↦ Hom(I^n, F)` obtained by taking `G` to be the
structure module. -/
noncomputable abbrev idealSheafPowerHomDiagram {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (F : X.Modules) : ℕ ⥤ AddCommGrpCat.{u + 1} :=
  idealPowerProductHomDiagram I (SheafOfModules.unit (structureSheaf X)) F

/-- The canonical additive comparison from `colim_n Hom(I^n, F)` to
`Hom(𝒪_U, F|_U)` on the complement of the closed subspace cut out by `I`. -/
noncomputable def idealSheafPowerHomColimitToComplementSections {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I]
    (F : X.Modules) :
    colimit (idealSheafPowerHomDiagram I F) ⟶
      AddCommGrpCat.of
        (SheafOfModules.unit (structureSheaf (idealOpenComplement I)) ⟶
          (restrictFunctor (idealOpenComplementι I)).obj F) :=
  idealPowerProductHomColimitToRestriction I
      (SheafOfModules.unit (structureSheaf X)) F ≫
    AddCommGrpCat.ofHom
      (Preadditive.leftComp ((restrictFunctor (idealOpenComplementι I)).obj F)
        (SheafOfModules.unitToPushforwardObjUnit
          (restrictStructureMap (idealOpenComplementι I))))

/-- On a Noetherian algebraic space, the canonical ideal-power Hom comparison to
sections on the complement is an isomorphism for every quasi-coherent module. -/
noncomputable instance idealSheafPowerHomColimitToComplementSections_isIso
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] (F : X.Modules)
    [F.IsQuasicoherent] :
    IsIso (idealSheafPowerHomColimitToComplementSections I F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
