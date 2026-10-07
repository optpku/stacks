module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import ReasLib.Algebra.Category.Ring.Sheaf.Units
public import ReasLib.CategoryTheory.Sites.Torsor.Basic
public import ReasLib.CategoryTheory.Sites.Torsor.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Picard classes and unit torsors

The local sheaf of generators of an invertible module carries a natural action by the sheaf of
units. Its torsor class gives the canonical comparison between Picard classes and first
cohomology classes.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PicardGroup

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The group-valued units sheaf used by the torsor construction. -/
@[stacks 040E "units group sheaf for the generator torsor"]
abbrev unitsGroup : Sheaf J GrpCat.{max u v} :=
  CategoryTheory.Sheaf.toSheafOfGroups (CategoryTheory.Sheaf.unitsAddSheaf 𝒪)

variable (ℒ : ringedSiteModuleCategory J 𝒪)

/-- The presheaf whose sections over `U` are local morphisms
`unitModule J 𝒪 | U ⟶ ℒ | U`. -/
@[stacks 040E "local generator morphism presheaf"]
abbrev localGeneratorPresheaf : Cᵒᵖ ⥤ Type (max u v) :=
  (InternalHom.obj 𝒪 (unitModule J 𝒪) ℒ).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat

/-- Restricting a local generator remains an isomorphism. -/
theorem localGenerator_restrict_isIso {U V : Cᵒᵖ} (i : U ⟶ V)
    (f : InternalHom.LocalHom 𝒪 (unitModule J 𝒪) ℒ U) (hf : IsIso f) :
    IsIso (InternalHom.restrictFun 𝒪 (unitModule J 𝒪) ℒ i f) := sorry

/-- The subpresheaf of local morphisms which are isomorphisms. -/
@[stacks 040E "local generator subpresheaf"]
noncomputable def localGeneratorSubfunctor :
    Subfunctor (localGeneratorPresheaf 𝒪 ℒ) where
  obj U := { f : InternalHom.LocalHom 𝒪 (unitModule J 𝒪) ℒ U | IsIso f }
  map i := fun f hf => localGenerator_restrict_isIso (𝒪 := 𝒪) (ℒ := ℒ) i f hf

/-- The local generator subpresheaf satisfies the sheaf condition. -/
@[stacks 040E "local generator sheaf condition"]
theorem localGenerator_isSheaf :
    Presheaf.IsSheaf J (localGeneratorSubfunctor 𝒪 ℒ).toFunctor := sorry

/-- The sheaf of local generators of an invertible module. -/
@[stacks 040E "sheaf of local generators"]
noncomputable def localGeneratorSheaf : Sheaf J (Type (max u v)) :=
  ⟨(localGeneratorSubfunctor 𝒪 ℒ).toFunctor, localGenerator_isSheaf 𝒪 ℒ⟩

/-- Convert a section of the additive presentation of the units sheaf to a ring unit. -/
@[stacks 040E "units section readout"]
def unitValue {U : Cᵒᵖ} (g : (unitsGroup 𝒪).1.obj U) : 𝒪.1.obj U :=
  CategoryTheory.Sheaf.unitsAddSheafValue 𝒪
    (CategoryTheory.Sheaf.toSheafOfGroupsValue
      (CategoryTheory.Sheaf.unitsAddSheaf 𝒪) g)

/-- Multiplication by a unit preserves the local-generator predicate. -/
theorem localGenerator_smul_isIso {U : Cᵒᵖ} (g : (unitsGroup 𝒪).1.obj U)
    (s : (localGeneratorSheaf 𝒪 ℒ).1.obj U) :
    IsIso (@SMul.smul _ _
      (InternalHom.homModule 𝒪 (unitModule J 𝒪) ℒ U).toSMul
      (unitValue 𝒪 g)
      (s.1 : InternalHom.LocalHom 𝒪 (unitModule J 𝒪) ℒ U)) := sorry

/-- The explicit unit action on local generators. -/
@[stacks 040E "unit action on local generators"]
noncomputable def localGeneratorAct {U : Cᵒᵖ} (g : (unitsGroup 𝒪).1.obj U)
    (s : (localGeneratorSheaf 𝒪 ℒ).1.obj U) :
    (localGeneratorSheaf 𝒪 ℒ).1.obj U :=
  ⟨@SMul.smul _ _
      (InternalHom.homModule 𝒪 (unitModule J 𝒪) ℒ U).toSMul
      (unitValue 𝒪 g)
      (s.1 : InternalHom.LocalHom 𝒪 (unitModule J 𝒪) ℒ U),
    localGenerator_smul_isIso 𝒪 ℒ g s⟩

/-- The unit element acts trivially on local generators. -/
theorem localGenerator_one_smul (U : C)
    (s : (localGeneratorSheaf 𝒪 ℒ).1.obj (op U)) :
    localGeneratorAct 𝒪 ℒ (1 : (unitsGroup 𝒪).1.obj (op U)) s = s := sorry

/-- Multiplication of units composes the local-generator action. -/
theorem localGenerator_mul_smul (U : C)
    (g h : (unitsGroup 𝒪).1.obj (op U))
    (s : (localGeneratorSheaf 𝒪 ℒ).1.obj (op U)) :
    localGeneratorAct 𝒪 ℒ (g * h) s =
      localGeneratorAct 𝒪 ℒ g (localGeneratorAct 𝒪 ℒ h s) := sorry

/-- The sectionwise unit action on the local-generator sheaf. -/
@[reducible, stacks 040E "local-generator sectionwise action"]
noncomputable def localGeneratorMulAction (U : C) :
    MulAction ((unitsGroup 𝒪).1.obj (op U))
      ((localGeneratorSheaf 𝒪 ℒ).1.obj (op U)) where
  smul := localGeneratorAct 𝒪 ℒ
  one_smul := localGenerator_one_smul 𝒪 ℒ U
  mul_smul := localGenerator_mul_smul 𝒪 ℒ U

/-- Units act on local generators by multiplication of the corresponding local morphisms. -/
instance localGeneratorMulAction_inst (U : C) :
    MulAction ((unitsGroup 𝒪).1.obj (op U))
      ((localGeneratorSheaf 𝒪 ℒ).1.obj (op U)) :=
  localGeneratorMulAction 𝒪 ℒ U

/-- The local-generator action is pretransitive. -/
theorem localGenerator_isPretransitive (U : C) :
    MulAction.IsPretransitive ((unitsGroup 𝒪).1.obj (op U))
      ((localGeneratorSheaf 𝒪 ℒ).1.obj (op U)) := sorry

/-- The local-generator action is free. -/
theorem localGenerator_isCancelSMul (U : C) :
    IsCancelSMul ((unitsGroup 𝒪).1.obj (op U))
      ((localGeneratorSheaf 𝒪 ℒ).1.obj (op U)) := sorry

/-- Restriction maps of local generators are equivariant for the unit action. -/
theorem localGenerator_act_naturality {U V : C} (f : V ⟶ U)
    (g : (unitsGroup 𝒪).1.obj (op U))
    (s : (localGeneratorSheaf 𝒪 ℒ).1.obj (op U)) :
    (localGeneratorSheaf 𝒪 ℒ).1.map f.op (localGeneratorAct 𝒪 ℒ g s) =
      localGeneratorAct 𝒪 ℒ ((unitsGroup 𝒪).1.map f.op g)
        ((localGeneratorSheaf 𝒪 ℒ).1.map f.op s) := sorry

/-- Local generators exist on a covering of every object. -/
theorem localGenerator_locallyNonempty [𝒪.IsLocallyRinged]
    [isInvertibleObject ℒ] (U : C) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
        Nonempty ((localGeneratorSheaf 𝒪 ℒ).1.obj (op V)) := sorry

/-- The torsor of local generators of an invertible module. -/
@[stacks 040E "generator torsor of an invertible module"]
noncomputable def localGeneratorTorsor [𝒪.IsLocallyRinged]
    [isInvertibleObject ℒ] : CategoryTheory.Sheaf.Torsor (unitsGroup 𝒪) where
  carrier := localGeneratorSheaf 𝒪 ℒ
  mulAction := localGeneratorMulAction 𝒪 ℒ
  act_naturality := localGenerator_act_naturality 𝒪 ℒ
  isPretransitive := localGenerator_isPretransitive 𝒪 ℒ
  isCancelSMul := localGenerator_isCancelSMul 𝒪 ℒ
  locallyNonempty := localGenerator_locallyNonempty 𝒪 ℒ

/-- The torsor class attached to a Picard class via its canonical invertible representative. -/
@[stacks 040E "Picard class to generator torsor class"]
noncomputable def generatorTorsorClass [𝒪.IsLocallyRinged]
    (x : PicardGroup J 𝒪) :
    CategoryTheory.Sheaf.Torsor.IsoClasses (unitsGroup 𝒪) :=
  _root_.Quotient.mk''
    (localGeneratorTorsor 𝒪 (MonoidalCategory.PicardGroup.repr x))

/-- The generator-torsor assignment is invariant under the Picard representative choice and is
bijective on isomorphism classes. -/
@[stacks 040E "Picard classes and generator torsor classes"]
theorem generatorTorsorClass_bijective [𝒪.IsLocallyRinged] :
    Function.Bijective (generatorTorsorClass 𝒪) := sorry

/-- Compose the generator-torsor assignment with any target-valued torsor-class map whose
normalization and tensor-additivity have been specified. -/
@[stacks 040E "Picard map through generator torsor classes"]
noncomputable def mapThroughTorsorClasses {β : Type*} [AddMonoid β]
    [𝒪.IsLocallyRinged]
    (κ : CategoryTheory.Sheaf.Torsor.IsoClasses (unitsGroup 𝒪) → β)
    (hκ_zero : κ (generatorTorsorClass 𝒪 0) = 0)
    (hκ_add : ∀ x y : PicardGroup J 𝒪,
      κ (generatorTorsorClass 𝒪 (x + y)) =
        κ (generatorTorsorClass 𝒪 x) + κ (generatorTorsorClass 𝒪 y)) :
    PicardGroup J 𝒪 →+ β where
  toFun := fun x ↦ κ (generatorTorsorClass 𝒪 x)
  map_zero' := hκ_zero
  map_add' := hκ_add

/-- The composed Picard map is bijective when the torsor assignment and target comparison are
bijective. -/
@[stacks 040E "bijectivity of the Picard torsor-class composition"]
theorem mapThroughTorsorClasses_bijective_of_bijective {β : Type*} [AddMonoid β]
    [𝒪.IsLocallyRinged]
    (κ : CategoryTheory.Sheaf.Torsor.IsoClasses (unitsGroup 𝒪) → β)
    (hκ_bijective : Function.Bijective κ)
    (hκ_zero : κ (generatorTorsorClass 𝒪 0) = 0)
    (hκ_add : ∀ x y : PicardGroup J 𝒪,
      κ (generatorTorsorClass 𝒪 (x + y)) =
        κ (generatorTorsorClass 𝒪 x) + κ (generatorTorsorClass 𝒪 y))
    :
    Function.Bijective (mapThroughTorsorClasses 𝒪 κ hκ_zero hκ_add) := sorry

section CohomologyClass

variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

/-- The torsor cohomology class of the neutral Picard class is zero. -/
theorem generatorCohomologyClass_zero [𝒪.IsLocallyRinged] :
    CategoryTheory.Sheaf.Torsor.Cohomology.classMap
        (CategoryTheory.Sheaf.unitsAddSheaf 𝒪) (generatorTorsorClass 𝒪 0) = 0 := sorry

/-- Tensor product of invertible modules adds their generator-torsor cohomology classes. -/
theorem generatorCohomologyClass_add [𝒪.IsLocallyRinged]
    (x y : PicardGroup J 𝒪) :
    CategoryTheory.Sheaf.Torsor.Cohomology.classMap
        (CategoryTheory.Sheaf.unitsAddSheaf 𝒪) (generatorTorsorClass 𝒪 (x + y)) =
      CategoryTheory.Sheaf.Torsor.Cohomology.classMap
          (CategoryTheory.Sheaf.unitsAddSheaf 𝒪) (generatorTorsorClass 𝒪 x) +
        CategoryTheory.Sheaf.Torsor.Cohomology.classMap
          (CategoryTheory.Sheaf.unitsAddSheaf 𝒪) (generatorTorsorClass 𝒪 y) := sorry

/-- The canonical additive homomorphism sends an invertible module to the first cohomology class
of its local-generator torsor. -/
@[stacks 040E "canonical Picard-to-cohomology map"]
noncomputable def cohomologyClass [𝒪.IsLocallyRinged] :
    PicardGroup J 𝒪 →+ (CategoryTheory.Sheaf.unitsAddSheaf 𝒪).H 1 :=
  mapThroughTorsorClasses 𝒪
    (CategoryTheory.Sheaf.Torsor.Cohomology.classMap
      (CategoryTheory.Sheaf.unitsAddSheaf 𝒪))
    (generatorCohomologyClass_zero 𝒪) (generatorCohomologyClass_add 𝒪)

/-- The canonical Picard-to-cohomology map is computed by the local-generator torsor class. -/
@[simp]
theorem cohomologyClass_apply [𝒪.IsLocallyRinged] (x : PicardGroup J 𝒪) :
    cohomologyClass 𝒪 x =
      CategoryTheory.Sheaf.Torsor.Cohomology.classMap
        (CategoryTheory.Sheaf.unitsAddSheaf 𝒪) (generatorTorsorClass 𝒪 x) := sorry

/-- The canonical Picard-to-first-cohomology homomorphism is bijective. -/
@[stacks 040E "canonical Picard-to-cohomology map is bijective"]
theorem cohomologyClass_bijective [𝒪.IsLocallyRinged] :
    Function.Bijective (cohomologyClass 𝒪) := sorry

end CohomologyClass

end SheafOfModules.RingedSite.PicardGroup
