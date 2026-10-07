module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap76.Lemma_76_42_4_Completion

/-!
# Internal Hom of coherent completions on algebraic spaces

The ideal-power quotients of the internal-Hom sheaf form an inverse system of
global sections. Evaluation of a compatible family at every quotient stage
gives a comparison from its inverse limit to morphisms of completed coherent
modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.IdealSheaf
open SheafOfModules.RingedSite.InternalHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A morphism of commutative `𝒪_X`-modules lifts on sections over `U` by
universe-lifting the component at `U`. -/
noncomputable def liftedSectionMap {F G : commModules X} (f : F ⟶ G)
    (U : (smallEtaleSite X)ᵒᵖ) :
    liftedSection F U ⟶ liftedSection G U :=
  eqToHom (liftedSection_eq F U).symm ≫
    (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).map
      ((ModuleCat.uliftFunctor.{u + 1, u} ((commStructureSheaf X).obj.obj U)).map
        (f.val.app U)) ≫
    eqToHom (liftedSection_eq G U)

/-- A morphism of commutative `𝒪_X`-modules lifts to the universe-lifted
presentation by applying `ULift` sectionwise. -/
noncomputable def liftCommModuleMap {F G : commModules X} (f : F ⟶ G) :
    liftCommModule F ⟶ liftCommModule G where
  val :=
    { app := fun U ↦ liftedSectionMap f U
      naturality := sorry }

/-- A morphism of `𝒪_X`-modules lifts to the universe-lifted commutative
presentation. -/
noncomputable def liftModuleMap {F G : X.Modules} (f : F ⟶ G) :
    liftModule F ⟶ liftModule G :=
  liftCommModuleMap ((toCommModules X).map f)

/-- Recover a morphism of commutative `𝒪_X`-modules from its universe lift by
evaluating `ULift.down` on sections. -/
noncomputable def unliftCommModuleHom {F G : commModules X}
    (f : liftCommModule F ⟶ liftCommModule G) : F ⟶ G where
  val :=
    { app := fun U ↦
        ModuleCat.ofHom
          { toFun := fun x ↦ (f.val.app U (ULift.up x)).down
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- Recover a morphism of `𝒪_X`-modules from a morphism of their universe
lifts, using the commutative presentation equivalence. -/
noncomputable def unliftModuleHom {F G : X.Modules}
    (f : liftModule F ⟶ liftModule G) : F ⟶ G :=
  (commModulesEquivalence X).counitIso.inv.app F ≫
    (ofCommModules X).map (unliftCommModuleHom f) ≫
    (commModulesEquivalence X).counitIso.hom.app G

/-- The component over `U` of the comparison from the universe lift of the
structure module to the tensor unit of the lifted commutative presentation. -/
noncomputable def liftedUnitComparisonApp (X : AlgebraicSpace S)
    (U : (smallEtaleSite X)ᵒᵖ) :
    liftedSection
        ((toCommModules X).obj (SheafOfModules.unit (structureSheaf X))) U ⟶
      (unitModule (smallEtaleTopology X) (commStructureSheafLift X)).val.obj U :=
  𝟙 _

/-- Comparison from the universe lift of the structure module to the tensor unit
of the lifted commutative presentation. -/
noncomputable def liftedUnitComparison (X : AlgebraicSpace S) :
    liftModule (SheafOfModules.unit (structureSheaf X)) ⟶
      unitModule (smallEtaleTopology X) (commStructureSheafLift X) where
  val :=
    { app := fun U ↦ liftedUnitComparisonApp X U
      naturality := sorry }

/-- The inclusion of a lifted ideal sheaf into the lifted structure module. -/
noncomputable def liftedIdealArrow (I : IdealSubobject X) :
    liftModule I.toModule ⟶
      unitModule (smallEtaleTopology X) (commStructureSheafLift X) :=
  liftModuleMap I.arrow ≫ liftedUnitComparison X

/-- The lifted ideal inclusion is a monomorphism. -/
instance liftedIdealArrow_mono (I : IdealSubobject X) :
    Mono (liftedIdealArrow I) := sorry

/-- An ideal subobject of `𝒪_X`, recast as a subobject of the universe-lifted
commutative structure module. -/
noncomputable def liftedIdealSubobject (I : IdealSubobject X) :
    Subobject (unitModule (smallEtaleTopology X) (commStructureSheafLift X)) :=
  Subobject.mk (liftedIdealArrow I)

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

open AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The ideal-power quotient `Hom(F, G) / I ^ n Hom(F, G)` on the universe-lifted
commutative presentation. -/
noncomputable abbrev homStage [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) (n : ℕ) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  PowerQuotientModule.stage.{u + 1, u, u + 1} (liftedIdealSubobject I)
    (internalHom F.obj G.obj) n

/-- The inverse system whose stage `n` consists of global sections of
`Hom(F, G) / I ^ n Hom(F, G)`. -/
noncomputable def homSectionsSystem [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) : ℕᵒᵖ ⥤ Type (u + 1) :=
  PowerQuotientModule.sectionsSystem.{u + 1, u, u + 1} (liftedIdealSubobject I)
    (internalHom F.obj G.obj)

/-- Stage `n` of the internal-Hom sections system is the type of global sections
of `Hom(F, G) / I ^ n Hom(F, G)`. -/
theorem homSectionsSystem_obj [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) (n : ℕ) :
    (homSectionsSystem I F G).obj (op n) = (homStage I F G n).sections := sorry

/-- The section represented by a compatible family in the inverse limit at
stage `n`. -/
noncomputable def homSection [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    (homStage I F G n).sections :=
  limit.π (homSectionsSystem I F G) (op n) x

/-- Evaluation of internal Hom against its source, as a morphism out of the
tensor product. -/
noncomputable def homEvaluation (F G : X.Modules) :
    tensorObj (liftModule F) (internalHom F G) ⟶ liftModule G :=
  (homEquiv (commStructureSheafLift X) (liftModule F) (internalHom F G)
      (liftModule G)).symm
    (𝟙 (internalHom F G))

/-- The reduced evaluation `F ⊗ Hom(F, G) ⟶ G / I ^ n G` vanishes on the
ideal-power action of `I ^ n` on internal Hom. -/
theorem homLeftDesc_zero [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) (n : ℕ) :
    (tensorLeft (liftModule F.obj)).map
          (powerAction (liftedIdealSubobject I) (internalHom F.obj G.obj) n) ≫
        homEvaluation F.obj G.obj ≫
          liftModuleMap (quotientByIdealPower.π I G.obj n) =
      0 := sorry

/-- The cokernel presentation of `F ⊗ (Hom / I ^ n Hom)` mapping to
`G / I ^ n G`. -/
noncomputable def homLeftDescCoker [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) (n : ℕ) :
    cokernel
        ((tensorLeft (liftModule F.obj)).map
          (powerAction (liftedIdealSubobject I) (internalHom F.obj G.obj) n)) ⟶
      liftModule (quotientByIdealPower I G.obj n) :=
  cokernel.desc
    ((tensorLeft (liftModule F.obj)).map
      (powerAction (liftedIdealSubobject I) (internalHom F.obj G.obj) n))
    (homEvaluation F.obj G.obj ≫
      liftModuleMap (quotientByIdealPower.π I G.obj n))
    (homLeftDesc_zero I F G n)

/-- Evaluation of internal Hom, reduced modulo `I ^ n` on the target and
factored through `Hom / I ^ n Hom`. -/
noncomputable def homLeftDesc [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) (n : ℕ) :
    (tensorLeft (liftModule F.obj)).obj (homStage I F G n) ⟶
      liftModule (quotientByIdealPower I G.obj n) :=
  (PreservesCokernel.iso (tensorLeft (liftModule F.obj))
        (powerAction (liftedIdealSubobject I) (internalHom F.obj G.obj) n)).hom ≫
    homLeftDescCoker I F G n

/-- The curried comparison `Hom / I ^ n Hom ⟶ Hom(F, G / I ^ n G)`. -/
noncomputable def homReduce [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) (n : ℕ) :
    homStage I F G n ⟶
      internalHom F.obj (quotientByIdealPower I G.obj n) :=
  homEquiv (commStructureSheafLift X) (liftModule F.obj) (homStage I F G n)
    (liftModule (quotientByIdealPower I G.obj n)) (homLeftDesc I F G n)

/-- A compatible internal-Hom quotient section determines a morphism
`F ⟶ G / I ^ n G` on universe-lifted modules. -/
noncomputable def homLiftedMap [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    liftModule F.obj ⟶ liftModule (quotientByIdealPower I G.obj n) :=
  sectionsHomEquiv (commStructureSheafLift X) (liftModule F.obj)
    (liftModule (quotientByIdealPower I G.obj n))
    (SheafOfModules.sectionsMap (homReduce I F G n) (homSection I F G x n))

/-- The unlifted morphism `F ⟶ G / I ^ n G` associated to a compatible
internal-Hom quotient section. -/
noncomputable def homUnliftedMap [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    F.obj ⟶ quotientByIdealPower I G.obj n :=
  unliftModuleHom (homLiftedMap I F G x n)

/-- The morphism `F ⟶ G / I ^ n G` associated to a compatible family vanishes
on `I ^ n F`. -/
theorem homUnliftedMap_comp_zero [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    (idealPowerProductSubobject I F.obj n).arrow ≫
        homUnliftedMap I F G x n =
      0 := sorry

/-- Evaluation of a compatible internal-Hom section on the stage-`n` ideal-power
quotients, as a morphism of underlying modules. -/
noncomputable def homQuotientMap [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    quotientByIdealPower I F.obj n ⟶ quotientByIdealPower I G.obj n :=
  cokernel.desc (idealPowerProductSubobject I F.obj n).arrow
    (homUnliftedMap I F G x n) (homUnliftedMap_comp_zero I F G x n)

/-- The map on coherent completion stages obtained by evaluating a compatible
internal-Hom family. -/
noncomputable def homComparisonStageMap [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    stage I F n ⟶ stage I G n :=
  ObjectProperty.homMk (homQuotientMap I F G x n)

/-- The stage maps defined by a compatible family commute with completion
transitions. -/
theorem homComparisonStageMap_naturality [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    (system I F).map (homOfLE (Nat.le_add_right n 1)).op ≫
        homComparisonStageMap I F G x n =
      homComparisonStageMap I F G x (n + 1) ≫
        (system I G).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- A compatible family of internal-Hom quotient sections determines a morphism
between the corresponding coherent completions. -/
noncomputable def homComparison [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) :
    limit (homSectionsSystem I F G) → (system I F ⟶ system I G) :=
  fun x ↦
    NatTrans.ofOpSequence (homComparisonStageMap I F G x)
      (homComparisonStageMap_naturality I F G x)

/-- Evaluating the Hom comparison at stage `n` recovers the stage morphism
associated to the compatible family. -/
theorem homComparison_apply [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    (homComparison I F G x).app (op n) =
      homComparisonStageMap I F G x n := sorry

/-- The canonical comparison from the inverse limit of internal-Hom quotient
sections to morphisms between coherent completions is bijective. -/
theorem homComparison_bijective [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) :
    Function.Bijective (homComparison I F G) := sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
