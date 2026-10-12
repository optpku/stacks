/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap69.Lemma_69_20_1_Tensor
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf

/-!
# Degree-one triples for relative Proj of algebraic spaces

A test object of the degree-one relative projective functor over an algebraic space is a
triple `(f, ℒ, ψ)` consisting of a morphism to the base, an invertible module, and a
graded algebra map inducing a surjection `f^* 𝒜_1 ⟶ ℒ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct
open AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Recover a morphism of commutative `𝒪_X`-modules from its universe lift. -/
def unliftCommModuleHom {F G : commModules X}
    (f : liftCommModule F ⟶ liftCommModule G) : F ⟶ G where
  val :=
    { app := fun U ↦
        ModuleCat.ofHom
          { toFun := fun x ↦ (f.val.app U (ULift.up x)).down
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- Recover a morphism of `𝒪_X`-modules from a morphism of their universe lifts. -/
def unliftModuleHom {F G : X.Modules} (f : liftModule F ⟶ liftModule G) : F ⟶ G :=
  (commModulesEquivalence X).counitIso.inv.app F ≫
    (ofCommModules X).map (unliftCommModuleHom f) ≫
    (commModulesEquivalence X).counitIso.hom.app G

/-- Base change of schemes étale over `Z` along `f ≫ g` identifies with base change
along `g` followed by spaces-étale pullback along `f`. -/
def etaleBaseChangeComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ spacesEtalePullback f :=
  (smallEtaleInclusion_comp_spacesEtalePullback (f ≫ g)).symm ≪≫
    isoWhiskerLeft (smallEtaleInclusion Z) (spacesEtalePullbackComp f g) ≪≫
    isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback g) (spacesEtalePullback f)

/-- `pullbackCompIso` is the left-adjoint mate of `pushforwardComp`. -/
theorem pullbackCompIso_eq {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCompIso f g =
      Adjunction.leftAdjointCompIso
        (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (f ≫ g)) (pushforwardComp f g) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The degree-`n` piece of a graded algebra sheaf on the universe-lifted commutative small
étale site of an algebraic space. -/
abbrev degreeModule (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (n : ℕ) : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  𝒜.obj (Int.ofNat n)

/-- `degreeModule 𝒜 n` is the degree-`n` summand of `𝒜`. -/
theorem degreeModule_eq (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (n : ℕ) : degreeModule 𝒜 n = 𝒜.obj (Int.ofNat n) :=
  rfl

/-- Sections of `liftModule F` are universe-lifted commutative sections. -/
theorem liftModule_val_obj_eq {Y : AlgebraicSpace S} (F : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (Modules.liftModule F).val.obj U =
      Modules.liftedSection ((Modules.toCommModules Y).obj F) U :=
  sorry

/-- Reidentify a section of `liftModule F` as a universe-lifted commutative section. -/
def asLiftedSection {Y : AlgebraicSpace S} (F : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) (x : (Modules.liftModule F).val.obj U) :
    Modules.liftedSection ((Modules.toCommModules Y).obj F) U :=
  eqToHom (liftModule_val_obj_eq F U) x

/-- Reidentify a universe-lifted commutative section as a section of `liftModule F`. -/
def ofLiftedSection {Y : AlgebraicSpace S} (F : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x : Modules.liftedSection ((Modules.toCommModules Y).obj F) U) :
    (Modules.liftModule F).val.obj U :=
  eqToHom (liftModule_val_obj_eq F U).symm x

/-- Universe-lift a commutative section of a commutative module sheaf. -/
def upLiftedCommSection {Y : AlgebraicSpace S} (F : Modules.commModules Y)
    (U : (smallEtaleSite Y)ᵒᵖ) (x : F.val.obj U) :
    Modules.liftedSection F U :=
  eqToHom (Modules.liftedSection_eq F U).symm (ULift.up x)

/-- Pointwise pure tensor of commutative module sections. -/
def commPointwiseTensor {Y : AlgebraicSpace S} {A B : Modules.commModules Y}
    (U : (smallEtaleSite Y)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (PresheafOfModules.Monoidal.tensorObj A.val B.val).obj U :=
  x ⊗ₜ y

/-- Sheaf morphism from the sheafified pointwise tensor of `toComm F` and `toComm G` to
`toComm (F ⊗ G)`. -/
def commTensorComparison {Y : AlgebraicSpace S} (F G : Y.Modules) :
    (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).obj
      (PresheafOfModules.Monoidal.tensorObj
        ((Modules.toCommModules Y).obj F).val
        ((Modules.toCommModules Y).obj G).val) ⟶
      (Modules.toCommModules Y).obj (F ⊗ G) :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
      ((Modules.toCommModules Y).obj F).val
      ((Modules.toCommModules Y).obj G).val).inv ≫
    tensorHom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((Modules.toCommModules Y).obj F)).hom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((Modules.toCommModules Y).obj G)).hom ≫
    (Modules.commModulesEquivalence Y).unit.app
      (CategoryTheory.MonoidalCategory.tensorObj
        ((Modules.toCommModules Y).obj F)
        ((Modules.toCommModules Y).obj G))

/-- Pure tensor of already-unlifted commutative sections, as a section of `lift (F ⊗ G)`. -/
def commTensorToLift {Y : AlgebraicSpace S} (F G : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x : ((Modules.toCommModules Y).obj F).val.obj U)
    (y : ((Modules.toCommModules Y).obj G).val.obj U) :
    Modules.liftedSection ((Modules.toCommModules Y).obj (F ⊗ G)) U :=
  upLiftedCommSection ((Modules.toCommModules Y).obj (F ⊗ G)) U
    ((commTensorComparison F G).val.app U
      ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf Y)
          (PresheafOfModules.Monoidal.tensorObj
            ((Modules.toCommModules Y).obj F).val
            ((Modules.toCommModules Y).obj G).val)).app U
        (commPointwiseTensor U x y)))

/-- Universe-lift of a pure tensor of unlifted modules, as a section of
`lift (F ⊗ G)`. -/
def liftModuleTensorSection {Y : AlgebraicSpace S} (F G : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x : (Modules.liftModule F).val.obj U)
    (y : (Modules.liftModule G).val.obj U) :
    (Modules.liftModule (F ⊗ G)).val.obj U :=
  ofLiftedSection (F ⊗ G) U
    (commTensorToLift F G U (asLiftedSection F U x).down (asLiftedSection G U y).down)

/-- Right-linear pure tensoring into `lift (F ⊗ G)`. -/
def liftModuleTensorRight {Y : AlgebraicSpace S} (F G : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x : (Modules.liftModule F).val.obj U) :
    (Modules.liftModule G).val.obj U →ₗ[(commStructureSheafLift Y).obj.obj U]
      (Modules.liftModule (F ⊗ G)).val.obj U where
  toFun y := liftModuleTensorSection F G U x y
  map_add' := sorry
  map_smul' := sorry

/-- The objectwise bilinear map of lifted sections into `lift (F ⊗ G)`. -/
def liftModuleTensorApp {Y : AlgebraicSpace S} (F G : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (Modules.liftModule F).val.obj U →ₗ[(commStructureSheafLift Y).obj.obj U]
      (Modules.liftModule G).val.obj U →ₗ[(commStructureSheafLift Y).obj.obj U]
        (Modules.liftModule (F ⊗ G)).val.obj U where
  toFun x := liftModuleTensorRight F G U x
  map_add' := sorry
  map_smul' := sorry

/-- Compatible bilinear map of lifted sections representing `liftModuleTensorHom`. -/
def liftModuleTensorBilinear {Y : AlgebraicSpace S} (F G : Y.Modules) :
    PresheafOfModules.BilinearMap (commStructureSheafLift Y).obj
      (Modules.liftModule F).val (Modules.liftModule G).val
      (Modules.liftModule (F ⊗ G)).val where
  app := liftModuleTensorApp F G
  naturality := sorry

/-- The sheafification comparison identifying `lift F ⊗ lift G` with the sheafification of
the pointwise tensor of underlying lifted presheaves. -/
def liftModuleTensorSheafify {Y : AlgebraicSpace S} (F G : Y.Modules) :
    tensorObj (Modules.liftModule F) (Modules.liftModule G) ⟶
      (moduleSheafification (commStructureSheafLift Y)).obj
        (PresheafOfModules.Monoidal.tensorObj
          (Modules.liftModule F).val (Modules.liftModule G).val) :=
  tensorHom
      (moduleSheafificationValIso (commStructureSheafLift Y)
        (Modules.liftModule F)).inv
      (moduleSheafificationValIso (commStructureSheafLift Y)
        (Modules.liftModule G)).inv ≫
    Functor.LaxMonoidal.μ (moduleSheafification (commStructureSheafLift Y))
      (Modules.liftModule F).val (Modules.liftModule G).val

/-- The lax comparison `lift F ⊗ lift G ⟶ lift (F ⊗ G)`, obtained by universe-lifting the
pure tensor of the commutative presentations. -/
def liftModuleTensorHom {Y : AlgebraicSpace S} (F G : Y.Modules) :
    tensorObj (Modules.liftModule F) (Modules.liftModule G) ⟶
      Modules.liftModule (F ⊗ G) :=
  liftModuleTensorSheafify F G ≫
    (moduleSheafificationHomEquiv (commStructureSheafLift Y)
        (PresheafOfModules.Monoidal.tensorObj
          (Modules.liftModule F).val (Modules.liftModule G).val)
        (Modules.liftModule (F ⊗ G))).symm
      (liftModuleTensorBilinear F G).toHom


/-- Unlifted homogeneous pieces of a graded algebra sheaf, identified with the universe-lifted
components after `liftModule`, together with the unlifted multiplication of homogeneous
pieces. -/
structure DegreePieces {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) where
  /-- The unlifted degree-`n` piece as an `𝒪_X`-module. -/
  obj : ℕ → X.Modules
  /-- Universe lift recovers the homogeneous component of `𝒜`. -/
  iso : ∀ n : ℕ, Modules.liftModule (obj n) ≅ degreeModule 𝒜 n
  /-- Unlifted multiplication of homogeneous pieces. -/
  mul : ∀ i j : ℕ, obj i ⊗ obj j ⟶ obj (i + j)
  /-- Unlifted multiplication is the transport of `GradedAlgebraSheaf.mulHom` along `iso`. -/
  mul_spec : ∀ i j : ℕ,
    liftModuleTensorHom (obj i) (obj j) ≫ Modules.liftModuleMap (mul i j) =
      ((iso i).hom ⊗ₘ (iso j).hom) ≫
        GradedAlgebraSheaf.mulHom 𝒜 (Int.ofNat i) (Int.ofNat j) ≫
          eqToHom (congrArg 𝒜.obj (Int.natCast_add i j).symm) ≫
            (iso (i + j)).inv

namespace DegreePieces

/-- Construct unlifted degree pieces from a family of modules, comparison isomorphisms, and
homogeneous multiplication. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (obj : ℕ → X.Modules)
    (iso : ∀ n : ℕ, Modules.liftModule (obj n) ≅ degreeModule 𝒜 n)
    (mul : ∀ i j : ℕ, obj i ⊗ obj j ⟶ obj (i + j))
    (mul_spec : ∀ i j : ℕ,
      liftModuleTensorHom (obj i) (obj j) ≫ Modules.liftModuleMap (mul i j) =
        ((iso i).hom ⊗ₘ (iso j).hom) ≫
          GradedAlgebraSheaf.mulHom 𝒜 (Int.ofNat i) (Int.ofNat j) ≫
            eqToHom (congrArg 𝒜.obj (Int.natCast_add i j).symm) ≫
              (iso (i + j)).inv) :
    DegreePieces 𝒜 where
  obj := obj
  iso := iso
  mul := mul
  mul_spec := mul_spec

/-- Universe lift of `deg.obj n` is the degree-`n` piece of `𝒜`. -/
def iso_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (n : ℕ) :
    Modules.liftModule (deg.obj n) ≅ degreeModule 𝒜 n :=
  deg.iso n

/-- `iso_spec deg n` is the stored comparison isomorphism. -/
theorem iso_spec_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (n : ℕ) :
    iso_spec deg n = deg.iso n :=
  rfl

end DegreePieces

/-- Tensor powers of an `𝒪_Y`-module based at the structure module `𝒪_Y`. -/
abbrev tensorPowerUnit {Y : AlgebraicSpace S} (L : Y.Modules) (n : ℕ) : Y.Modules :=
  tensorPowerWithDegreeZero (SheafOfModules.unit (structureSheaf Y)) L n

/-- The zeroth unit-based tensor power is the structure module. -/
theorem tensorPowerUnit_zero {Y : AlgebraicSpace S} (L : Y.Modules) :
    tensorPowerUnit L 0 = SheafOfModules.unit (structureSheaf Y) :=
  tensorPowerWithDegreeZero_zero (SheafOfModules.unit (structureSheaf Y)) L

/-- The successor unit-based tensor power is left tensor with `L`. -/
theorem tensorPowerUnit_succ {Y : AlgebraicSpace S} (L : Y.Modules) (n : ℕ) :
    tensorPowerUnit L (n + 1) = L ⊗ tensorPowerUnit L n :=
  rfl

/-- Concatenation of unit-based tensor powers. -/
def tensorPowerUnitAddIso {Y : AlgebraicSpace S} (L : Y.Modules) (i j : ℕ) :
    tensorPowerUnit L i ⊗ tensorPowerUnit L j ≅ tensorPowerUnit L (i + j) :=
  tensorPowerWithDegreeZeroAddIso (Modules.structureModuleIsoTensorUnit Y) L i j

/-- The induced map of unit-based tensor powers along a module morphism. -/
def tensorPowerUnitMap {Y : AlgebraicSpace S} {L L' : Y.Modules} (β : L ⟶ L') (n : ℕ) :
    tensorPowerUnit L n ⟶ tensorPowerUnit L' n :=
  tensorPowerWithDegreeZeroMap (SheafOfModules.unit (structureSheaf Y)) β n

/-- Universe-lifted tensor powers of an `𝒪_Y`-module. -/
abbrev tensorPowerSheaf {Y : AlgebraicSpace S} (L : Y.Modules) (n : ℕ) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift Y) :=
  TensorPower.sheaf (commStructureSheafLift Y) (Modules.liftModule L) n

/-- The degree-zero unit morphism of a graded algebra sheaf. -/
def gradedOneHom (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) :
    unitModule (smallEtaleTopology X) (commStructureSheafLift X) ⟶ degreeModule 𝒜 0 where
  val :=
    { app := fun U ↦
        ModuleCat.ofHom
          { toFun := fun r ↦ r • 𝒜.one U
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- The unlifted degree-zero unit of a graded algebra sheaf. -/
def degreeZeroUnit {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) :
    SheafOfModules.unit (structureSheaf X) ⟶ deg.obj 0 :=
  Modules.unliftModuleHom
    ((Modules.liftedUnitIso X).hom ≫ gradedOneHom 𝒜 ≫ (deg.iso 0).inv)

/-- The structure-sheaf unit of `Y` as a local section of its universe lift. -/
def liftedUnitSection (Y : AlgebraicSpace S) (U : (smallEtaleSite Y)ᵒᵖ) :
    (unitModule (smallEtaleTopology Y) (commStructureSheafLift Y)).val.obj U :=
  TensorPower.oneSection (commStructureSheafLift Y)
    (Modules.liftModule (SheafOfModules.unit (structureSheaf Y))) U

/-- Pullback of the degree-zero unit along `f`, as a section of the universe-lifted
pullback of `𝒜_0`. -/
def psiSourceOneSection {Y : AlgebraicSpace S} (f : Y ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (U : (smallEtaleSite Y)ᵒᵖ) :
    (Modules.liftModule ((Modules.pullback f).obj (deg.obj 0))).val.obj U :=
  ((Modules.liftModuleMap
        (Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map (degreeZeroUnit deg))).val.app U).hom
    (((Modules.liftedUnitIso Y).inv.val.app U).hom (liftedUnitSection Y U))

/-- The pullback-side source of a homogeneous component of `ψ`. -/
abbrev psiSource {Y : AlgebraicSpace S} (f : Y ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (n : ℕ) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift Y) :=
  Modules.liftModule ((Modules.pullback f).obj (deg.obj n))

/-- Transport a morphism out of a commutative tensor product to `Y.Modules`. -/
def modulesTensorHom {Y : AlgebraicSpace S} {F G H : Y.Modules}
    (φ : (Modules.toCommModules Y).obj F ⊗ (Modules.toCommModules Y).obj G ⟶
      (Modules.toCommModules Y).obj H) : F ⊗ G ⟶ H :=
  (Modules.ofCommModules Y).map φ ≫
    (Modules.commModulesEquivalence Y).counitIso.hom.app H

/-- The type-valued sheaf underlying an `𝒪`-module. -/
abbrev moduleUnderlying {Y : AlgebraicSpace S} (M : Y.Modules) :
    Sheaf (smallEtaleTopology Y) (Type u) :=
  (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj M

/-- Charts of `Z ×_Y V` in the small étale site of `Z`. -/
abbrev pushforwardCharts {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (V : smallEtaleSite Y) :=
  StructuredArrow (op ((etaleBaseChange h).obj V)) (smallEtaleInclusion Z).op

/-- Restriction of scalars along `commRingSheafIso` does not change the section carrier. -/
theorem toCommModules_val_obj {Y : AlgebraicSpace S} (M : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    ((Modules.toCommModules Y).obj M).val.obj U = M.val.obj U :=
  sorry

/-- View a module section as a section of its commutative presentation. -/
def asCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    ((Modules.toCommModules Y).obj M).val.obj U :=
  eqToHom (toCommModules_val_obj M U).symm s

/-- View a commutative presentation section as a section of the original module. -/
def ofCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : ((Modules.toCommModules Y).obj M).val.obj U) :
    M.val.obj U :=
  eqToHom (toCommModules_val_obj M U) s

/-- The spaces-étale extension of the type-valued sheaf underlying an `𝒪_Z`-module. -/
def moduleSpacesPushforward {Z : AlgebraicSpace S} (M : Z.Modules) :
    Sheaf (spacesEtaleTopology Z) (Type u) :=
  ((smallEtaleInclusion Z).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology Z) (spacesEtaleTopology Z)).obj
    (moduleUnderlying M)

/-- Sections of the spaces-étale extension of `M` at `Z ×_Y V`. -/
def moduleSpacesSectionAt {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) : Type u :=
  (moduleSpacesPushforward M).obj.obj (op ((etaleBaseChange h).obj V))

/-- Forget module structure on a pushed-forward section at a small-étale object of `Y`. -/
def modulePushforwardForgetSection {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y)
    (s : ((Modules.pushforward h).obj M).val.obj (op V)) :
    ((typePushforward h).obj (moduleUnderlying M)).obj.obj (op V) :=
  ((RingedSite.ToposHom.ModulePushforward.forgetIso
      (ringedToposHom h)).hom.app M).hom.app (op V) s

/-- Type-valued pushforward at `V` is the spaces-étale extension evaluated at `Z ×_Y V`. -/
theorem typePushforward_eval {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) :
    ((typePushforward h).obj (moduleUnderlying M)).obj.obj (op V) =
      moduleSpacesSectionAt h M V :=
  sorry

/-- The spaces-étale extension is the right Kan extension of the underlying presheaf. -/
theorem moduleSpacesPushforward_ran {Z : AlgebraicSpace S} (M : Z.Modules)
    (W : (spacesEtaleSite Z)ᵒᵖ) :
    (moduleSpacesPushforward M).obj.obj W =
      ((smallEtaleInclusion Z).op.ran.obj (moduleUnderlying M).obj).obj W :=
  sorry

/-- Chartwise sections at `Z ×_Y V` are spaces-étale sections of the extension. -/
theorem moduleSpacesSectionAt_eq {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) :
    moduleSpacesSectionAt h M V =
      (moduleSpacesPushforward M).obj.obj (op ((etaleBaseChange h).obj V)) :=
  sorry

/-- Reidentify a forgotten `h_* M` section at `V` as a spaces-étale section at `Z ×_Y V`. -/
def modulePushforwardSpacesSection {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y)
    (s : ((Modules.pushforward h).obj M).val.obj (op V)) :
    moduleSpacesSectionAt h M V :=
  eqToHom (typePushforward_eval h M V)
    (modulePushforwardForgetSection h M V s)

/-- Reidentify a spaces-étale section at `Z ×_Y V` as a forgotten `h_* M` section at `V`. -/
def modulePushforwardFromSpacesSection {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y)
    (t : moduleSpacesSectionAt h M V) :
    ((typePushforward h).obj (moduleUnderlying M)).obj.obj (op V) :=
  eqToHom (typePushforward_eval h M V).symm t

/-- The right Kan extension of the type-valued sheaf underlying an `𝒪_Z`-module. -/
abbrev moduleRan {Z : AlgebraicSpace S} (M : Z.Modules) :
    (spacesEtaleSite Z)ᵒᵖ ⥤ Type u :=
  (smallEtaleInclusion Z).op.ran.obj (moduleUnderlying M).obj

/-- Restrict a Kan-extended section along a structured arrow of the small étale inclusion. -/
def moduleRanRestrict {Z : AlgebraicSpace S} (M : Z.Modules)
    (W : spacesEtaleSite Z) (c : StructuredArrow (op W) (smallEtaleInclusion Z).op)
    (t : (moduleRan M).obj (op W)) :
    (moduleRan M).obj ((smallEtaleInclusion Z).op.obj c.right) :=
  (moduleRan M).map c.hom t

/-- Apply the Kan counit to recover a small-étale section. -/
def moduleRanCounitApp {Z : AlgebraicSpace S} (M : Z.Modules)
    (U : (smallEtaleSite Z)ᵒᵖ)
    (t : (moduleRan M).obj ((smallEtaleInclusion Z).op.obj U)) :
    (moduleUnderlying M).obj.obj U :=
  ((smallEtaleInclusion Z).op.ranCounit.app (moduleUnderlying M).obj).app U t

/-- Restrict a spaces-étale extension section along a small-étale chart. -/
def moduleSpacesChartRestrict {Z : AlgebraicSpace S} (M : Z.Modules)
    (W : spacesEtaleSite Z) (c : StructuredArrow (op W) (smallEtaleInclusion Z).op)
    (t : (moduleSpacesPushforward M).obj.obj (op W)) :
    (moduleUnderlying M).obj.obj c.right :=
  moduleRanCounitApp M c.right
    (moduleRanRestrict M W c (eqToHom (moduleSpacesPushforward_ran M (op W)) t))

/-- The type-valued underlying sheaf has the same sections as the module sheaf. -/
theorem moduleUnderlying_obj {Y : AlgebraicSpace S} (M : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (moduleUnderlying M).obj.obj U = M.val.obj U :=
  sorry

/-- Reidentify an underlying type-valued section as a module section. -/
def ofUnderlyingSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : (moduleUnderlying M).obj.obj U) :
    M.val.obj U :=
  eqToHom (moduleUnderlying_obj M U) s

/-- Reidentify a module section as an underlying type-valued section. -/
def toUnderlyingSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    (moduleUnderlying M).obj.obj U :=
  eqToHom (moduleUnderlying_obj M U).symm s

/-- `toUnderlyingSection` inverts `ofUnderlyingSection` on the underlying carrier. -/
theorem toUnderlyingSection_spec {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    toUnderlyingSection M s = eqToHom (moduleUnderlying_obj M U).symm s :=
  sorry

/-- Restrict a spaces-étale section of a pushed-forward module along a chart of `Z ×_Y V`. -/
def moduleSpacesChartRestrictPush {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) (c : pushforwardCharts h V)
    (t : moduleSpacesSectionAt h M V) :
    (moduleUnderlying M).obj.obj c.right :=
  moduleRanCounitApp M c.right
    (moduleRanRestrict M ((etaleBaseChange h).obj V) c
      (eqToHom (moduleSpacesPushforward_ran M (op ((etaleBaseChange h).obj V)))
        (eqToHom (moduleSpacesSectionAt_eq h M V) t)))

/-- Evaluate a pushed-forward module section at a small-étale chart of `Z ×_Y V`. -/
def moduleChartValue {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M : Z.Modules) (V : smallEtaleSite Y) (c : pushforwardCharts h V)
    (s : ((Modules.pushforward h).obj M).val.obj (op V)) :
    (moduleUnderlying M).obj.obj c.right :=
  moduleSpacesChartRestrictPush h M V c (modulePushforwardSpacesSection h M V s)

/-- Pure tensor of commutative presentations, transported to `toComm (M ⊗ N)`. -/
def commTensorSection {Y : AlgebraicSpace S} (M N : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ}
    (x : ((Modules.toCommModules Y).obj M).val.obj U)
    (y : ((Modules.toCommModules Y).obj N).val.obj U) :
    ((Modules.toCommModules Y).obj (M ⊗ N)).val.obj U :=
  (commTensorComparison M N).val.app U
    ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf Y)
        (PresheafOfModules.Monoidal.tensorObj
          ((Modules.toCommModules Y).obj M).val
          ((Modules.toCommModules Y).obj N).val)).app U
      (commPointwiseTensor U x y))

/-- `commTensorSection` is `commTensorComparison` applied to a pointwise pure tensor. -/
theorem commTensorSection_spec {Y : AlgebraicSpace S} (M N : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ}
    (x : ((Modules.toCommModules Y).obj M).val.obj U)
    (y : ((Modules.toCommModules Y).obj N).val.obj U) :
    commTensorSection M N x y =
      (commTensorComparison M N).val.app U
        ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf Y)
            (PresheafOfModules.Monoidal.tensorObj
              ((Modules.toCommModules Y).obj M).val
              ((Modules.toCommModules Y).obj N).val)).app U
          (commPointwiseTensor U x y)) :=
  sorry

/-- Pure tensor of chartwise evaluations, as a section of `M ⊗ N` on the chart. -/
def moduleChartTensor {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M N : Z.Modules) (V : smallEtaleSite Y) (c : pushforwardCharts h V)
    (x : ((Modules.pushforward h).obj M).val.obj (op V))
    (y : ((Modules.pushforward h).obj N).val.obj (op V)) :
    (moduleUnderlying (M ⊗ N)).obj.obj c.right :=
  toUnderlyingSection (M ⊗ N)
    (ofCommSection (M ⊗ N)
      (commTensorSection M N
        (asCommSection M (ofUnderlyingSection M (moduleChartValue h M V c x)))
        (asCommSection N (ofUnderlyingSection N (moduleChartValue h N V c y)))))

/-- Cone of chartwise pure tensors presenting the pushforward-tensor comparison at `V`. -/
def pushforwardTensorCone {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M N : Z.Modules) (V : smallEtaleSite Y)
    (x : ((Modules.pushforward h).obj M).val.obj (op V))
    (y : ((Modules.pushforward h).obj N).val.obj (op V)) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange h).obj V))
        (smallEtaleInclusion Z).op ⋙ (moduleUnderlying (M ⊗ N)).obj) where
  pt := PUnit
  π :=
    { app := fun c => TypeCat.ofHom fun _ => moduleChartTensor h M N V c x y
      naturality := sorry }

/-- Assemble chartwise pure tensors to a section of `h_*(M ⊗ N)` at `V`. -/
def pushforwardTensorSection {Y Z : AlgebraicSpace S}
    (h : Z ⟶ Y) (M N : Z.Modules) (V : smallEtaleSite Y)
    (x : ((Modules.pushforward h).obj M).val.obj (op V))
    (y : ((Modules.pushforward h).obj N).val.obj (op V)) :
    ((Modules.pushforward h).obj (M ⊗ N)).val.obj (op V) :=
  ((RingedSite.ToposHom.ModulePushforward.forgetIso
      (ringedToposHom h)).inv.app (M ⊗ N)).hom.app (op V)
    (modulePushforwardFromSpacesSection h (M ⊗ N) V
      (eqToHom (moduleSpacesSectionAt_eq h (M ⊗ N) V).symm
        (eqToHom (moduleSpacesPushforward_ran (M ⊗ N)
              (op ((etaleBaseChange h).obj V))).symm
          (((smallEtaleInclusion Z).op.ranObjObjIsoLimit
              (moduleUnderlying (M ⊗ N)).obj
              (op ((etaleBaseChange h).obj V))).inv
            (limit.lift _ (pushforwardTensorCone h M N V x y) PUnit.unit)))))

/-- Compatible bilinear map of commutative presentations representing the
pushforward tensorator. -/
def pushforwardTensorBilinear {Y Z : AlgebraicSpace S}
    (h : Z ⟶ Y) (M N : Z.Modules) :
    PresheafOfModules.BilinearMap (commStructureSheaf Y).obj
      ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj M)).val
      ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj N)).val
      ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj (M ⊗ N))).val where
  app V :=
    { toFun := fun x =>
        { toFun := fun y =>
            asCommSection ((Modules.pushforward h).obj (M ⊗ N))
              (pushforwardTensorSection h M N V.unop
                (ofCommSection ((Modules.pushforward h).obj M) x)
                (ofCommSection ((Modules.pushforward h).obj N) y))
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- The lax comparison `(h_* M) ⊗ (h_* N) ⟶ h_*(M ⊗ N)`, obtained by descending
the chartwise pure-tensor pairing of pushed-forward sections. -/
def pushforwardTensorLax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (M N : Z.Modules) :
    (Modules.pushforward h).obj M ⊗ (Modules.pushforward h).obj N ⟶
      (Modules.pushforward h).obj (M ⊗ N) :=
  modulesTensorHom
    (tensorHom
        (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
          ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj M))).inv
        (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
          ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj N))).inv ≫
      Functor.LaxMonoidal.μ
        (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
        ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj M)).val
        ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj N)).val ≫
      (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).map
        (PresheafOfModules.BilinearMap.toHom (pushforwardTensorBilinear h M N)) ≫
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((Modules.toCommModules Y).obj ((Modules.pushforward h).obj (M ⊗ N)))).hom)

/-- The oplax comparison `h^*(A ⊗ B) ⟶ h^* A ⊗ h^* B`, the adjunction transpose of the
tensor of units followed by `pushforwardTensorLax`. -/
def pullbackTensorOplax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (Modules.pullback h).obj (A ⊗ B) ⟶
      (Modules.pullback h).obj A ⊗ (Modules.pullback h).obj B :=
  ((Modules.pullbackPushforwardAdjunction h).homEquiv
      (A ⊗ B)
      ((Modules.pullback h).obj A ⊗ (Modules.pullback h).obj B)).symm
    (((Modules.pullbackPushforwardAdjunction h).unit.app A ⊗ₘ
        (Modules.pullbackPushforwardAdjunction h).unit.app B) ≫
      pushforwardTensorLax h
        ((Modules.pullback h).obj A) ((Modules.pullback h).obj B))

/-- The oplax pullback-tensor comparison is an isomorphism. -/
instance instIsIso_pullbackTensorOplax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (A B : Y.Modules) :
    IsIso (pullbackTensorOplax h A B) :=
  sorry

/-- The lax comparison `h^* A ⊗ h^* B ⟶ h^*(A ⊗ B)`, the inverse of
`pullbackTensorOplax`. -/
def pullbackTensorLax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (Modules.pullback h).obj A ⊗ (Modules.pullback h).obj B ⟶
      (Modules.pullback h).obj (A ⊗ B) :=
  inv (pullbackTensorOplax h A B)

/-- Source multiplication of pulled-back homogeneous sections, using the unlifted
multiplication of `deg` after the lift laxator and the pullback laxator. -/
def psiSourceMulHom {Y : AlgebraicSpace S} (f : Y ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (i j : ℕ) :
    tensorObj (psiSource f deg i) (psiSource f deg j) ⟶ psiSource f deg (i + j) :=
  liftModuleTensorHom
      ((Modules.pullback f).obj (deg.obj i))
      ((Modules.pullback f).obj (deg.obj j)) ≫
    Modules.liftModuleMap
      (pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
        (Modules.pullback f).map (deg.mul i j))

/-- The product of two pulled-back homogeneous sections of `𝒜`. -/
def psiSourceMulSection {Y : AlgebraicSpace S} (f : Y ⟶ X)
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (U : (smallEtaleSite Y)ᵒᵖ) (i j : ℕ)
    (x : (psiSource f deg i).val.obj U) (y : (psiSource f deg j).val.obj U) :
    (psiSource f deg (i + j)).val.obj U :=
  ((Modules.liftModuleMap
        (pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
          (Modules.pullback f).map (deg.mul i j))).val.app U).hom
    (liftModuleTensorSection
      ((Modules.pullback f).obj (deg.obj i))
      ((Modules.pullback f).obj (deg.obj j)) U x y)

/-- Lifted multiplication of homogeneous pieces of `𝒜` recovers `mulHom` after the stored
degreewise identifications. -/
theorem degreeMul_spec {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (deg : DegreePieces 𝒜) (i j : ℕ) :
    liftModuleTensorHom (deg.obj i) (deg.obj j) ≫ Modules.liftModuleMap (deg.mul i j) =
      ((deg.iso i).hom ⊗ₘ (deg.iso j).hom) ≫
        GradedAlgebraSheaf.mulHom 𝒜 (Int.ofNat i) (Int.ofNat j) ≫
          eqToHom (congrArg 𝒜.obj (Int.natCast_add i j).symm) ≫
            (deg.iso (i + j)).inv :=
  sorry

/-- Pullback of the structure module along `h`. -/
def pullbackMonoidalUnitIso {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    (Modules.pullback h).obj (SheafOfModules.unit (structureSheaf Y)) ≅
      SheafOfModules.unit (structureSheaf Z) where
  hom := IdealSubobject.pullbackUnit h
  inv := Modules.structureModulePullbackInv h
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Pullback of a unit-based tensor power is the tensor power of the pullback, using the
structure-module comparison in degree zero and the pullback laxator in successor degrees. -/
def pullbackTensorPowerHom {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (L : Y.Modules) :
    (n : ℕ) →
      (Modules.pullback h).obj (tensorPowerUnit L n) ⟶
        tensorPowerUnit ((Modules.pullback h).obj L) n :=
  Nat.rec
    (eqToHom (congrArg (Modules.pullback h).obj (tensorPowerUnit_zero L)) ≫
      (pullbackMonoidalUnitIso h).hom ≫
        eqToHom (tensorPowerUnit_zero ((Modules.pullback h).obj L)).symm)
    (fun n rec ↦
      eqToHom (congrArg (Modules.pullback h).obj (tensorPowerUnit_succ L n)) ≫
        pullbackTensorOplax h L (tensorPowerUnit L n) ≫
          (𝟙 ((Modules.pullback h).obj L) ⊗ₘ rec) ≫
            eqToHom (tensorPowerUnit_succ ((Modules.pullback h).obj L) n).symm)

/-- A degree-one relative projective triple over a test scheme `T` over `S`. -/
structure DegreeOneTriple
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (deg : DegreePieces 𝒜) (T : Over S) where
  /-- The structure morphism `f : T ⟶ X` over `S`, as a morphism of algebraic spaces. -/
  morphism : ofOver T ⟶ X
  /-- The invertible `𝒪_T`-module. -/
  lineBundle : (ofOver T).Modules
  /-- Invertibility of the chosen module. -/
  lineBundle_invertible : isInvertibleObject lineBundle
  /-- Degreewise components of `ψ : f^* 𝒜 ⟶ ⊕_{n ≥ 0} ℒ^{⊗ n}` on the pullback side. -/
  psi : ∀ n : ℕ,
    (Modules.pullback morphism).obj (deg.obj n) ⟶ tensorPowerUnit lineBundle n
  /-- The degreewise map sends the pulled-back unit of `𝒜` to the tensor-power unit. -/
  psi_map_one :
    ∀ U : smallEtaleSite (ofOver T),
      (((Modules.liftModuleMap (psi 0)).val.app (op U)).hom)
          (psiSourceOneSection morphism deg (op U)) =
        ((Modules.liftedUnitIso (ofOver T)).hom.val.app (op U)).hom
          (TensorPower.oneSection (commStructureSheafLift (ofOver T))
            (Modules.liftModule lineBundle) (op U))
  /-- The degreewise map preserves multiplication of homogeneous sections against
  `TensorPower.mulSection`. -/
  psi_map_mul :
    ∀ (U : smallEtaleSite (ofOver T)) (i j : ℕ)
      (x : (psiSource morphism deg i).val.obj (op U))
      (y : (psiSource morphism deg j).val.obj (op U)),
      (((Modules.liftModuleMap (psi (i + j))).val.app (op U)).hom)
          (psiSourceMulSection morphism deg (op U) i j x y) =
        ((Modules.liftModuleMap
            (tensorPowerUnitAddIso lineBundle i j).hom).val.app (op U)).hom
          (liftModuleTensorSection
            (tensorPowerUnit lineBundle i)
            (tensorPowerUnit lineBundle j) (op U)
            (((Modules.liftModuleMap (psi i)).val.app (op U)).hom x)
            (((Modules.liftModuleMap (psi j)).val.app (op U)).hom y))
  /-- The pullback-side degree-one map. -/
  degreeOneMap :
    (Modules.pullback morphism).obj (deg.obj 1) ⟶ tensorPowerUnit lineBundle 1
  /-- The displayed degree-one map is the degree-one component of `ψ`. -/
  degreeOneMap_spec : degreeOneMap = psi 1
  /-- The degree-one map is an epimorphism. -/
  degreeOne_surjective : Epi degreeOneMap

namespace DegreeOneTriple

/-- Construct a degree-one triple from a morphism, invertible module, graded map, unit and
multiplication laws, and the pullback-side degree-one epimorphism. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S}
    (morphism : ofOver T ⟶ X) (lineBundle : (ofOver T).Modules)
    (lineBundle_invertible : isInvertibleObject lineBundle)
    (psi : ∀ n : ℕ,
      (Modules.pullback morphism).obj (deg.obj n) ⟶ tensorPowerUnit lineBundle n)
    (psi_map_one :
      ∀ U : smallEtaleSite (ofOver T),
        (((Modules.liftModuleMap (psi 0)).val.app (op U)).hom)
            (psiSourceOneSection morphism deg (op U)) =
          ((Modules.liftedUnitIso (ofOver T)).hom.val.app (op U)).hom
            (TensorPower.oneSection (commStructureSheafLift (ofOver T))
              (Modules.liftModule lineBundle) (op U)))
    (psi_map_mul :
      ∀ (U : smallEtaleSite (ofOver T)) (i j : ℕ)
        (x : (psiSource morphism deg i).val.obj (op U))
        (y : (psiSource morphism deg j).val.obj (op U)),
        (((Modules.liftModuleMap (psi (i + j))).val.app (op U)).hom)
            (psiSourceMulSection morphism deg (op U) i j x y) =
          ((Modules.liftModuleMap
              (tensorPowerUnitAddIso lineBundle i j).hom).val.app (op U)).hom
            (liftModuleTensorSection
              (tensorPowerUnit lineBundle i)
              (tensorPowerUnit lineBundle j) (op U)
              (((Modules.liftModuleMap (psi i)).val.app (op U)).hom x)
              (((Modules.liftModuleMap (psi j)).val.app (op U)).hom y)))
    (degreeOneMap :
      (Modules.pullback morphism).obj (deg.obj 1) ⟶ tensorPowerUnit lineBundle 1)
    (degreeOneMap_spec : degreeOneMap = psi 1)
    (degreeOne_surjective : Epi degreeOneMap) :
    DegreeOneTriple 𝒜 deg T where
  morphism := morphism
  lineBundle := lineBundle
  lineBundle_invertible := lineBundle_invertible
  psi := psi
  psi_map_one := psi_map_one
  psi_map_mul := psi_map_mul
  degreeOneMap := degreeOneMap
  degreeOneMap_spec := degreeOneMap_spec
  degreeOne_surjective := degreeOne_surjective

/-- The invertibility, unit, multiplication, and degree-one epimorphism conditions hold
simultaneously. -/
theorem conditions_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : DegreeOneTriple 𝒜 deg T) :
    isInvertibleObject q.lineBundle ∧
      (∀ U : smallEtaleSite (ofOver T),
        (((Modules.liftModuleMap (q.psi 0)).val.app (op U)).hom)
            (psiSourceOneSection q.morphism deg (op U)) =
          ((Modules.liftedUnitIso (ofOver T)).hom.val.app (op U)).hom
            (TensorPower.oneSection (commStructureSheafLift (ofOver T))
              (Modules.liftModule q.lineBundle) (op U))) ∧
      (∀ (U : smallEtaleSite (ofOver T)) (i j : ℕ)
        (x : (psiSource q.morphism deg i).val.obj (op U))
        (y : (psiSource q.morphism deg j).val.obj (op U)),
        (((Modules.liftModuleMap (q.psi (i + j))).val.app (op U)).hom)
            (psiSourceMulSection q.morphism deg (op U) i j x y) =
          ((Modules.liftModuleMap
              (tensorPowerUnitAddIso q.lineBundle i j).hom).val.app (op U)).hom
            (liftModuleTensorSection
              (tensorPowerUnit q.lineBundle i)
              (tensorPowerUnit q.lineBundle j) (op U)
              (((Modules.liftModuleMap (q.psi i)).val.app (op U)).hom x)
              (((Modules.liftModuleMap (q.psi j)).val.app (op U)).hom y))) ∧
      (q.degreeOneMap = q.psi 1) ∧
      Epi q.degreeOneMap :=
  sorry

/-- The pullback-side degree-one map of a triple. -/
def degreeMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : DegreeOneTriple 𝒜 deg T) :
    (Modules.pullback q.morphism).obj (deg.obj 1) ⟶ tensorPowerUnit q.lineBundle 1 :=
  q.degreeOneMap

/-- `degreeMap q` is `q.degreeOneMap`. -/
theorem degreeMap_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : DegreeOneTriple 𝒜 deg T) :
    degreeMap q = q.degreeOneMap :=
  rfl

/-- `degreeOneMap q` is the degree-one component of `q.psi`. -/
theorem degreeOneMap_spec_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S} (q : DegreeOneTriple 𝒜 deg T) :
    q.degreeOneMap = q.psi 1 :=
  q.degreeOneMap_spec

/-- Two triples are strictly equivalent when they have the same structure morphism and an
isomorphism of line bundles intertwining every homogeneous component of `ψ`. -/
def StrictlyEquivalent {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S}
    (q q' : DegreeOneTriple 𝒜 deg T) : Prop :=
  ∃ (h : q.morphism = q'.morphism) (β : q.lineBundle ≅ q'.lineBundle),
    ∀ n : ℕ,
      eqToHom (congrArg (fun f ↦ (Modules.pullback f).obj (deg.obj n)) h) ≫
          q'.psi n =
        q.psi n ≫ tensorPowerUnitMap β.hom n

/-- Strict equivalence is equality of structure morphisms together with a line-bundle
isomorphism transporting every homogeneous map. -/
theorem strictlyEquivalent_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T : Over S}
    (q q' : DegreeOneTriple 𝒜 deg T) :
    StrictlyEquivalent q q' ↔
      ∃ (h : q.morphism = q'.morphism) (β : q.lineBundle ≅ q'.lineBundle),
        ∀ n : ℕ,
          eqToHom (congrArg (fun f ↦ (Modules.pullback f).obj (deg.obj n)) h) ≫
              q'.psi n =
            q.psi n ≫ tensorPowerUnitMap β.hom n :=
  sorry

/-- The structure morphism of the pullback of a triple along a morphism of test schemes. -/
def pullbackMorphism {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) : ofOver T' ⟶ X :=
  ofOverMap g ≫ q.morphism

/-- The line bundle of the pullback of a triple is the module pullback of the original
line bundle. -/
def pullbackLineBundle {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) : (ofOver T').Modules :=
  (Modules.pullback (ofOverMap g)).obj q.lineBundle

/-- Homogeneous components of the pullback of a triple. -/
def pullbackPsi {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) (n : ℕ) :
    (Modules.pullback (pullbackMorphism g q)).obj (deg.obj n) ⟶
      tensorPowerUnit (pullbackLineBundle g q) n :=
  ((AlgebraicGeometry.AlgebraicSpace.Modules.pullbackCompIso
        (ofOverMap g) q.morphism).inv.app (deg.obj n)) ≫
    (Modules.pullback (ofOverMap g)).map (q.psi n) ≫
      pullbackTensorPowerHom (ofOverMap g) q.lineBundle n

/-- The pullback-side degree-one map of a pulled-back triple. -/
def pullbackDegreeOneMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) :
    (Modules.pullback (pullbackMorphism g q)).obj (deg.obj 1) ⟶
      tensorPowerUnit (pullbackLineBundle g q) 1 :=
  pullbackPsi g q 1

/-- Pull back a degree-one triple along a morphism of test schemes. -/
def pullback {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) : DegreeOneTriple 𝒜 deg T' :=
  of (pullbackMorphism g q) (pullbackLineBundle g q) sorry (pullbackPsi g q) sorry sorry
    (pullbackDegreeOneMap g q) sorry sorry

/-- The structure morphism of `pullback g q` is `ofOverMap g ≫ q.morphism`. -/
theorem pullback_morphism {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) :
    (pullback g q).morphism = ofOverMap g ≫ q.morphism :=
  rfl

/-- The line bundle of `pullback g q` is the module pullback of `q.lineBundle`. -/
theorem pullback_lineBundle {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} {T T' : Over S} (g : T' ⟶ T)
    (q : DegreeOneTriple 𝒜 deg T) :
    (pullback g q).lineBundle = (Modules.pullback (ofOverMap g)).obj q.lineBundle :=
  rfl

end DegreeOneTriple

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
