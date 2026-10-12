/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_65_1_Forward
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Module sheaves from finite continuous representations

The underlying finite locally constant sheaf comes from the set-level Galois
equivalence. Module operations are transported as equivariant maps and evaluated
sectionwise. No inverse of the module-valued forward equivalence is used.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped FintypeCatDiscrete

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleSheafInverse

variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable {X : Scheme.{u}} [ConnectedSpace X]
variable (xbar : GeometricPoint X)

/-- A finite-type module over the finite coefficient ring has finite underlying carrier. -/
instance finiteCarrier
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Finite M.obj.obj.V :=
  (Module.finite_iff_finite (R := Λ)).mp M.property

/-- A small model of the finite coefficient carrier, with its canonical equivalence. -/
abbrev Carrier
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) : Type u :=
  Shrink.{u} M.obj.obj.V

/-- The canonical equivalence to the small coefficient carrier. -/
def carrierEquiv
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    M.obj.obj.V ≃ Carrier Λ xbar M := equivShrink.{u} M.obj.obj.V

/-- The representation's action transported to the small finite carrier. -/
def smallAction
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Action FintypeCat.{u} (Aut (standardFiniteEtaleFiber xbar)) where
  V := FintypeCat.of (Carrier Λ xbar M)
  ρ :=
    { toFun := fun g ↦ FintypeCat.homMk fun m ↦
        carrierEquiv Λ xbar M ((M.obj.obj.ρ g).hom ((carrierEquiv Λ xbar M).symm m))
      map_one' := by
        apply ConcreteCategory.hom_ext
        intro m
        change carrierEquiv Λ xbar M ((M.obj.obj.ρ 1).hom ((carrierEquiv Λ xbar M).symm m)) = m
        simp
      map_mul' := fun g h ↦ by
        apply ConcreteCategory.hom_ext
        intro m
        change carrierEquiv Λ xbar M ((M.obj.obj.ρ (g * h)).hom
          ((carrierEquiv Λ xbar M).symm m)) =
            carrierEquiv Λ xbar M ((M.obj.obj.ρ g).hom ((carrierEquiv Λ xbar M).symm
              (carrierEquiv Λ xbar M ((M.obj.obj.ρ h).hom ((carrierEquiv Λ xbar M).symm m)))))
        simp [map_mul] }

/-- Open stabilizers of the original discrete representation give a continuous finite action. -/
theorem smallAction_continuous
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    (smallAction Λ xbar M).IsContinuous := sorry

/-- The finite continuous set underlying the coefficient representation. -/
def moduleSet
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    ContAction FintypeCat.{u} (Aut (standardFiniteEtaleFiber xbar)) :=
  ⟨smallAction Λ xbar M, smallAction_continuous Λ xbar M⟩

/-- The diagonal action on two copies of the small coefficient carrier. -/
def pairAction
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Action FintypeCat.{u} (Aut (standardFiniteEtaleFiber xbar)) where
  V := FintypeCat.of (Carrier Λ xbar M × Carrier Λ xbar M)
  ρ :=
    { toFun := fun g ↦ FintypeCat.homMk fun p ↦
        (((smallAction Λ xbar M).ρ g).hom p.1, ((smallAction Λ xbar M).ρ g).hom p.2)
      map_one' := by
        apply ConcreteCategory.hom_ext
        intro p
        change (((smallAction Λ xbar M).ρ 1).hom p.1,
          ((smallAction Λ xbar M).ρ 1).hom p.2) = p
        simp
      map_mul' := fun g h ↦ by
        apply ConcreteCategory.hom_ext
        intro p
        change (((smallAction Λ xbar M).ρ (g * h)).hom p.1,
          ((smallAction Λ xbar M).ρ (g * h)).hom p.2) =
            (((smallAction Λ xbar M).ρ g).hom (((smallAction Λ xbar M).ρ h).hom p.1),
             ((smallAction Λ xbar M).ρ g).hom (((smallAction Λ xbar M).ρ h).hom p.2))
        rw [map_mul]
        rfl }

/-- The diagonal finite action is continuous. -/
theorem pairAction_continuous
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    (pairAction Λ xbar M).IsContinuous := sorry

/-- The finite continuous pair object for coefficient addition. -/
def pairSet
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    ContAction FintypeCat.{u} (Aut (standardFiniteEtaleFiber xbar)) :=
  ⟨pairAction Λ xbar M, pairAction_continuous Λ xbar M⟩

/-- The one-point finite continuous action. -/
def unitSet : ContAction FintypeCat.{u} (Aut (standardFiniteEtaleFiber xbar)) :=
  ⟨Action.trivial (Aut (standardFiniteEtaleFiber xbar)) (FintypeCat.of PUnit.{u + 1}), by
    constructor
    change Continuous (fun _ : Aut (standardFiniteEtaleFiber xbar) × PUnit.{u + 1} ↦ PUnit.unit)
    exact continuous_const⟩

variable (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory)

/-- The first projection of the diagonal coefficient action. -/
def pairFst : pairSet Λ xbar M ⟶ moduleSet Λ xbar M :=
  ObjectProperty.homMk { hom := FintypeCat.homMk Prod.fst, comm := fun _ ↦ rfl }

/-- The second projection of the diagonal coefficient action. -/
def pairSnd : pairSet Λ xbar M ⟶ moduleSet Λ xbar M :=
  ObjectProperty.homMk { hom := FintypeCat.homMk Prod.snd, comm := fun _ ↦ rfl }

/-- The zero vector as an equivariant map from the one-point action. -/
def zeroMap : unitSet xbar ⟶ moduleSet Λ xbar M :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk fun _ ↦ carrierEquiv Λ xbar M 0
      comm := fun g ↦ by
        apply FintypeCat.hom_ext
        intro m
        change carrierEquiv Λ xbar M 0 =
          carrierEquiv Λ xbar M ((M.obj.obj.ρ g).hom
            ((carrierEquiv Λ xbar M).symm (carrierEquiv Λ xbar M 0)))
        simp }

/-- Coefficient addition as an equivariant map from the diagonal pair action. -/
def addMap : pairSet Λ xbar M ⟶ moduleSet Λ xbar M :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk fun p ↦ carrierEquiv Λ xbar M
        ((carrierEquiv Λ xbar M).symm p.1 + (carrierEquiv Λ xbar M).symm p.2)
      comm := fun g ↦ by
        apply FintypeCat.hom_ext
        intro p
        change carrierEquiv Λ xbar M
          (((carrierEquiv Λ xbar M).symm (carrierEquiv Λ xbar M
            ((M.obj.obj.ρ g).hom ((carrierEquiv Λ xbar M).symm p.1)))) +
           ((carrierEquiv Λ xbar M).symm (carrierEquiv Λ xbar M
            ((M.obj.obj.ρ g).hom ((carrierEquiv Λ xbar M).symm p.2))))) =
          carrierEquiv Λ xbar M ((M.obj.obj.ρ g).hom ((carrierEquiv Λ xbar M).symm
            (carrierEquiv Λ xbar M ((carrierEquiv Λ xbar M).symm p.1 +
              (carrierEquiv Λ xbar M).symm p.2))))
        simp }

/-- Coefficient negation as an equivariant map. -/
def negMap : moduleSet Λ xbar M ⟶ moduleSet Λ xbar M :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk fun m ↦ carrierEquiv Λ xbar M (- (carrierEquiv Λ xbar M).symm m)
      comm := fun g ↦ by
        apply FintypeCat.hom_ext
        intro m
        change carrierEquiv Λ xbar M (- (carrierEquiv Λ xbar M).symm
          (carrierEquiv Λ xbar M ((M.obj.obj.ρ g).hom ((carrierEquiv Λ xbar M).symm m)))) =
          carrierEquiv Λ xbar M ((M.obj.obj.ρ g).hom ((carrierEquiv Λ xbar M).symm
            (carrierEquiv Λ xbar M (- (carrierEquiv Λ xbar M).symm m))))
        simp }

/-- Scalar multiplication is equivariant because the coefficient action is Λ-linear. -/
def smulMap (a : Λ) : moduleSet Λ xbar M ⟶ moduleSet Λ xbar M :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk fun m ↦ carrierEquiv Λ xbar M (a • (carrierEquiv Λ xbar M).symm m)
      comm := fun g ↦ by
        apply FintypeCat.hom_ext
        intro m
        change carrierEquiv Λ xbar M (a • (carrierEquiv Λ xbar M).symm
          (carrierEquiv Λ xbar M ((M.obj.obj.ρ g).hom ((carrierEquiv Λ xbar M).symm m)))) =
          carrierEquiv Λ xbar M ((M.obj.obj.ρ g).hom ((carrierEquiv Λ xbar M).symm
            (carrierEquiv Λ xbar M (a • (carrierEquiv Λ xbar M).symm m))))
        simp }

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]

/-- The underlying set sheaf is the inverse of the existing finite-set Galois equivalence. -/
abbrev setSheaf (S : ContAction FintypeCat.{u} (Aut (standardFiniteEtaleFiber xbar))) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).inverse.obj S).obj

/-- Transport an equivariant set map through the set-level equivalence. -/
def setSheafMap
    {S T : ContAction FintypeCat.{u} (Aut (standardFiniteEtaleFiber xbar))} (f : S ⟶ T) :
    setSheaf xbar S ⟶ setSheaf xbar T :=
  ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).inverse.map f).hom

/-- The specified counit on underlying finite actions, before the module-stalk comparison. -/
def underlyingSetCounit :
    (finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj
      ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).inverse.obj (moduleSet Λ xbar M)) ≅
        moduleSet Λ xbar M :=
  (finiteLocallyConstant_equivalence_finitePi1Sets xbar).counitIso.app (moduleSet Λ xbar M)

/-- Sections of the underlying sheaf on an étale object. -/
abbrev Sections (U : X.Etaleᵒᵖ) : Type (u + 1) :=
  (setSheaf xbar (moduleSet Λ xbar M)).obj.obj U

/-- The specified map comparing pair-valued sections with pairs of sections. -/
def pairSections (U : X.Etaleᵒᵖ) :
    (setSheaf xbar (pairSet Λ xbar M)).obj.obj U → Sections Λ xbar M U × Sections Λ xbar M U :=
  fun s ↦ (((setSheafMap xbar (pairFst Λ xbar M)).hom.app U) s,
    ((setSheafMap xbar (pairSnd Λ xbar M)).hom.app U) s)

/-- The inverse set equivalence and the sheaf inclusion preserve the specified finite product. -/
theorem pairSections_bijective (U : X.Etaleᵒᵖ) :
    Function.Bijective (pairSections Λ xbar M U) := sorry

/-- The actual inverse of the pair-section comparison. -/
def pairSectionsEquiv (U : X.Etaleᵒᵖ) :
    (setSheaf xbar (pairSet Λ xbar M)).obj.obj U ≃ Sections Λ xbar M U × Sections Λ xbar M U :=
  Equiv.ofBijective (pairSections Λ xbar M U) (pairSections_bijective Λ xbar M U)

/-- Sections of the sheaf of the one-point action form a singleton. -/
theorem unitSections_bijective (U : X.Etaleᵒᵖ) :
    Function.Bijective (fun _ : (setSheaf xbar (unitSet xbar)).obj.obj U ↦ PUnit.unit :
      (setSheaf xbar (unitSet xbar)).obj.obj U → PUnit.{1}) := sorry

/-- The canonical unique section of the one-point sheaf. -/
def unitSection (U : X.Etaleᵒᵖ) : (setSheaf xbar (unitSet xbar)).obj.obj U :=
  (Equiv.ofBijective (fun _ : (setSheaf xbar (unitSet xbar)).obj.obj U ↦ (PUnit.unit : PUnit.{1}))
    (unitSections_bijective xbar U)).symm PUnit.unit

/-- Zero transported from the coefficient representation. -/
def sectionZero (U : X.Etaleᵒᵖ) : Sections Λ xbar M U :=
  ((setSheafMap xbar (zeroMap Λ xbar M)).hom.app U) (unitSection xbar U)

/-- Addition transported through the canonical pair-section comparison. -/
def sectionAdd (U : X.Etaleᵒᵖ) (s t : Sections Λ xbar M U) : Sections Λ xbar M U :=
  ((setSheafMap xbar (addMap Λ xbar M)).hom.app U)
    ((pairSectionsEquiv Λ xbar M U).symm (s, t))

/-- Negation transported from the coefficient representation. -/
def sectionNeg (U : X.Etaleᵒᵖ) (s : Sections Λ xbar M U) : Sections Λ xbar M U :=
  ((setSheafMap xbar (negMap Λ xbar M)).hom.app U) s

/-- Scalar multiplication transported from the coefficient representation. -/
def sectionSMul (U : X.Etaleᵒᵖ) (a : Λ) (s : Sections Λ xbar M U) : Sections Λ xbar M U :=
  ((setSheafMap xbar (smulMap Λ xbar M a)).hom.app U) s

/-- The transported zero section. -/
instance sectionsZero (U : X.Etaleᵒᵖ) : Zero (Sections Λ xbar M U) :=
  ⟨sectionZero Λ xbar M U⟩

/-- The transported addition of sections. -/
instance sectionsAdd (U : X.Etaleᵒᵖ) : Add (Sections Λ xbar M U) :=
  ⟨sectionAdd Λ xbar M U⟩

/-- The transported negation of sections. -/
instance sectionsNeg (U : X.Etaleᵒᵖ) : Neg (Sections Λ xbar M U) :=
  ⟨sectionNeg Λ xbar M U⟩

/-- Sections inherit the transported additive operations of the coefficient module. -/
instance sectionsAddCommGroup (U : X.Etaleᵒᵖ) : AddCommGroup (Sections Λ xbar M U) where
  zero := sectionZero Λ xbar M U
  add := sectionAdd Λ xbar M U
  neg := sectionNeg Λ xbar M U
  sub s t := sectionAdd Λ xbar M U s (sectionNeg Λ xbar M U t)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  neg_add_cancel := sorry
  add_comm := sorry
  sub_eq_add_neg := fun _ _ ↦ rfl

/-- The transported scalar maps give the section module structure. -/
instance sectionsModule (U : X.Etaleᵒᵖ) : Module Λ (Sections Λ xbar M U) where
  smul := sectionSMul Λ xbar M U
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Restriction uses the actual underlying sheaf restriction, now as a linear map. -/
def restrict {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    Sections Λ xbar M U →ₗ[Λ] Sections Λ xbar M V where
  toFun := (setSheaf xbar (moduleSet Λ xbar M)).obj.map f
  map_add' := sorry
  map_smul' := sorry

/-- The module-valued presheaf with transported operations and actual sheaf restrictions. -/
def presheaf : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj U := ModuleCat.of Λ (Sections Λ xbar M U)
  map f := ModuleCat.ofHom (restrict Λ xbar M f)
  map_id U := by
    ext s
    exact congrArg (fun f ↦ f s) ((setSheaf xbar (moduleSet Λ xbar M)).obj.map_id U)
  map_comp f g := by
    ext s
    exact congrArg (fun f ↦ f s) ((setSheaf xbar (moduleSet Λ xbar M)).obj.map_comp f g)

/-- Forgetting the transported operations recovers the original set-valued sheaf presheaf. -/
theorem presheaf_forget :
    presheaf Λ xbar M ⋙ CategoryTheory.forget (ModuleCat.{u + 1} Λ) =
      (setSheaf xbar (moduleSet Λ xbar M)).obj := rfl

/-- Module gluing is inherited from the actual underlying set sheaf via the forgetful functor. -/
theorem presheaf_isSheaf : Presheaf.IsSheaf X.smallEtaleTopology (presheaf Λ xbar M) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology (presheaf Λ xbar M)
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).mpr
  exact (setSheaf xbar (moduleSet Λ xbar M)).property

/-- The module sheaf associated to the finite continuous representation by transported operations. -/
def sheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ⟨presheaf Λ xbar M, presheaf_isSheaf Λ xbar M⟩

/-- The associated sheaf has exactly the set-equivalence inverse as its underlying presheaf. -/
theorem sheaf_forget :
    (sheaf Λ xbar M).obj ⋙ CategoryTheory.forget (ModuleCat.{u + 1} Λ) =
      (setSheaf xbar (moduleSet Λ xbar M)).obj := rfl

/-- A coefficient morphism on the finite underlying action retains its original function. -/
def moduleSetMap
    {M N : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory}
    (f : M ⟶ N) : moduleSet Λ xbar M ⟶ moduleSet Λ xbar N :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk fun m ↦ carrierEquiv Λ xbar N
        (f.hom.hom.hom.hom ((carrierEquiv Λ xbar M).symm m))
      comm := fun _ ↦ sorry }

/-- The associated morphism of module sheaves is the transported equivariant set map. -/
def sheafMap
    {M N : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory}
    (f : M ⟶ N) : sheaf Λ xbar M ⟶ sheaf Λ xbar N where
  hom :=
    { app U := ModuleCat.ofHom
        { toFun := ((setSheafMap xbar (moduleSetMap Λ xbar f)).hom.app U)
          map_add' := sorry
          map_smul' := sorry }
      naturality := fun U V g ↦ by
        ext s
        exact congrArg (fun h ↦ h s)
          ((setSheafMap xbar (moduleSetMap Λ xbar f)).hom.naturality g) }

/-- The prescribed associated-sheaf map respects coefficient identities. -/
theorem sheafMap_id
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    sheafMap Λ xbar (𝟙 M) = 𝟙 (sheaf Λ xbar M) := sorry

/-- The prescribed associated-sheaf map respects coefficient composition. -/
theorem sheafMap_comp
    {M N P : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory}
    (f : M ⟶ N) (g : N ⟶ P) :
    sheafMap Λ xbar (f ≫ g) = sheafMap Λ xbar f ≫ sheafMap Λ xbar g := sorry

/-- The concrete associated-module-sheaf functor, independent of the old module-equivalence inverse. -/
def functor :
    (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj M := sheaf Λ xbar M
  map f := sheafMap Λ xbar f
  map_id M := sheafMap_id Λ xbar M
  map_comp f g := sheafMap_comp Λ xbar f g

variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The transported finite module operations are locally constant of finite type. -/
theorem sheaf_finiteTypeLocallyConstant :
    Sheaf.IsFiniteTypeLocallyConstantModule (sheaf Λ xbar M) := sorry

/-- The same concrete inverse construction, with its finite locally constant property recorded. -/
def finiteFunctor :
    (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory ⥤
      (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory :=
  (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).lift
    (functor Λ xbar) (fun M ↦ sheaf_finiteTypeLocallyConstant Λ xbar M)

end AlgebraicGeometry.Scheme.ModuleSheafInverse
