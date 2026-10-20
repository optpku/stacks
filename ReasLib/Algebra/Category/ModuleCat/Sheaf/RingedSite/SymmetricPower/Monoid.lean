/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.NatMonoidal
public import ReasLib.CategoryTheory.GradedObject.Monoid
public import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded symmetric algebra as a commutative monoid object

Symmetric powers, their multiplication maps, and the degree-zero unit assemble into a canonical
commutative monoid object in Mathlib's symmetric monoidal category of naturally graded module
sheaves.  Both the commutative-monoid functor and its standard forgetful views are exposed.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SymmetricPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The naturally graded object whose degree `n` is the symmetric-power sheaf `Sym^[n](F)`. -/
@[stacks 01CF "graded object of symmetric powers"]
noncomputable abbrev gradedObject (F : ringedSiteModuleCategory J O) :
    GradedObject ℕ (ringedSiteModuleCategory J O) :=
  sheaf O F

/-- The homogeneous degree-zero unit of the graded symmetric-power object. -/
@[stacks 01CF "unit of the graded symmetric monoid"]
noncomputable def gradedOne (F : ringedSiteModuleCategory J O) :
    𝟙_ (ringedSiteModuleCategory J O) ⟶ gradedObject O F 0 :=
  (unitIsoTensorUnit (J := J) (𝒪 := O)).inv ≫ one O F

/-- Multiplication between two homogeneous components of the graded symmetric-power object. -/
@[stacks 01CF "homogeneous multiplication of the graded symmetric monoid"]
noncomputable def gradedMul (F : ringedSiteModuleCategory J O) (n m : ℕ) :
    MonoidalCategory.tensorObj (gradedObject O F n) (gradedObject O F m) ⟶
      gradedObject O F (n + m) :=
  mul O F n m

/-- The assembled unit morphism of the naturally graded symmetric-power object. -/
noncomputable def oneHom (F : ringedSiteModuleCategory J O) :
    𝟙_ (GradedObject ℕ (ringedSiteModuleCategory J O)) ⟶ gradedObject O F :=
  GradedObject.Monoidal.oneHom (gradedObject O F) (gradedOne O F)

/-- The assembled multiplication morphism of the naturally graded symmetric-power object. -/
noncomputable def mulHom (F : ringedSiteModuleCategory J O) :
    gradedObject O F ⊗ gradedObject O F ⟶ gradedObject O F :=
  GradedObject.Monoidal.mulHom (gradedObject O F) (gradedMul O F)

/-- The assembled symmetric-power unit is a left identity. -/
theorem oneHom_mulHom (F : ringedSiteModuleCategory J O) :
    oneHom O F ▷ gradedObject O F ≫ mulHom O F =
      (λ_ (gradedObject O F)).hom := sorry

/-- The assembled symmetric-power unit is a right identity. -/
theorem mulHom_oneHom (F : ringedSiteModuleCategory J O) :
    gradedObject O F ◁ oneHom O F ≫ mulHom O F =
      (ρ_ (gradedObject O F)).hom := sorry

/-- The assembled symmetric-power multiplication is associative. -/
theorem mulHom_assoc (F : ringedSiteModuleCategory J O) :
    (mulHom O F ▷ gradedObject O F) ≫ mulHom O F =
      (α_ (gradedObject O F) (gradedObject O F) (gradedObject O F)).hom ≫
        (gradedObject O F ◁ mulHom O F) ≫ mulHom O F := sorry

/-- The assembled symmetric-power multiplication commutes with the graded braiding. -/
theorem mulHom_braiding (F : ringedSiteModuleCategory J O) :
    (β_ (gradedObject O F) (gradedObject O F)).hom ≫ mulHom O F =
      mulHom O F := sorry

/-- The canonical monoid-object structure on the naturally graded symmetric powers. -/
@[stacks 01CF "graded symmetric monoid object", implicit_reducible]
noncomputable def monObj (F : ringedSiteModuleCategory J O) :
    MonObj (gradedObject O F) :=
  GradedObject.Monoidal.monObj (gradedObject O F) (gradedOne O F) (gradedMul O F)
    (oneHom_mulHom O F) (mulHom_oneHom O F) (mulHom_assoc O F)

/-- The explicit commutativity structure for the canonical symmetric-power monoid object. -/
@[stacks 01CF "commutativity structure of the graded symmetric monoid"]
theorem isCommMonObj (F : ringedSiteModuleCategory J O) :
    @IsCommMonObj _ _ _ _ (gradedObject O F) (monObj O F) := sorry

/-- The symmetric algebra bundled in Mathlib's category of commutative monoid objects. -/
@[stacks 01CF "bundled graded symmetric algebra", implicit_reducible]
noncomputable def commMon (F : ringedSiteModuleCategory J O) :
    CommMon (GradedObject ℕ (ringedSiteModuleCategory J O)) :=
  @CommMon.mk _ _ _ _ (gradedObject O F) (monObj O F)
    (isCommMonObj O F)

/-- The underlying monoid object of the bundled graded symmetric algebra. -/
@[implicit_reducible]
noncomputable def mon (F : ringedSiteModuleCategory J O) :
    Mon (GradedObject ℕ (ringedSiteModuleCategory J O)) :=
  (commMon O F).toMon

/-- The underlying graded object of the bundled symmetric algebra is its symmetric-power family. -/
@[simp]
theorem mon_X (F : ringedSiteModuleCategory J O) :
    (mon O F).X = gradedObject O F := sorry

/-- The bundled symmetric-algebra unit is the unit assembled from degree zero. -/
@[simp]
theorem mon_one (F : ringedSiteModuleCategory J O) :
    η[(mon O F).X] = oneHom O F := sorry

/-- The bundled symmetric-algebra multiplication is assembled from homogeneous products. -/
@[simp]
theorem mon_mul (F : ringedSiteModuleCategory J O) :
    μ[(mon O F).X] = mulHom O F := sorry

/-- On degrees `(n, m)`, bundled symmetric multiplication is the fixed-degree product. -/
@[reassoc (attr := simp)]
theorem ι_mon_mul_add (F : ringedSiteModuleCategory J O) (n m : ℕ) :
    GradedObject.Monoidal.ιTensorObj (gradedObject O F) (gradedObject O F)
        n m (n + m) rfl ≫ μ[(mon O F).X] (n + m) = gradedMul O F n m := sorry

/-- The morphism of graded symmetric-power objects induced by a module-sheaf morphism. -/
noncomputable def mapHom {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    gradedObject O F ⟶ gradedObject O G :=
  fun n ↦ map O f n

/-- The degree-`n` component of the induced graded symmetric-power morphism. -/
@[simp]
theorem mapHom_apply {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) (n : ℕ) :
    mapHom O f n = map O f n := sorry

/-- The induced graded symmetric-power morphism preserves identity morphisms. -/
theorem mapHom_id (F : ringedSiteModuleCategory J O) :
    mapHom O (𝟙 F) = 𝟙 (gradedObject O F) := sorry

/-- The induced graded symmetric-power morphism preserves composition. -/
theorem mapHom_comp {F G H : ringedSiteModuleCategory J O}
    (f : F ⟶ G) (g : G ⟶ H) :
    mapHom O (f ≫ g) = mapHom O f ≫ mapHom O g := sorry

/-- Symmetric powers as a functor to naturally graded module sheaves. -/
@[stacks 01CF "graded symmetric-power functor"]
noncomputable def gradedObjectFunctor :
    ringedSiteModuleCategory J O ⥤ GradedObject ℕ (ringedSiteModuleCategory J O) where
  obj := gradedObject O
  map := mapHom O
  map_id := mapHom_id O
  map_comp := mapHom_comp O

/-- The induced graded symmetric-power morphism preserves the assembled unit. -/
theorem mapHom_one {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    oneHom O F ≫ mapHom O f = oneHom O G := sorry

/-- The induced graded symmetric-power morphism preserves the assembled multiplication. -/
theorem mapHom_mul {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    mulHom O F ≫ mapHom O f =
      (mapHom O f ⊗ₘ mapHom O f) ≫ mulHom O G := sorry

/-- The monoid-object morphism induced by a module-sheaf morphism. -/
noncomputable def monMap {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    mon O F ⟶ mon O G :=
  Mon.Hom.mk' (mapHom O f) (mapHom_one O f) (mapHom_mul O f)

/-- The degree-`n` component of the underlying symmetric-algebra monoid map. -/
@[simp]
theorem monMap_hom_apply
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) (n : ℕ) :
    (monMap O f).hom n = map O f n := sorry

/-- The symmetric-algebra monoid map associated to an identity is the identity. -/
theorem monMap_id (F : ringedSiteModuleCategory J O) :
    monMap O (𝟙 F) = 𝟙 (mon O F) := sorry

/-- Symmetric-algebra monoid maps preserve composition. -/
theorem monMap_comp {F G H : ringedSiteModuleCategory J O}
    (f : F ⟶ G) (g : G ⟶ H) :
    monMap O (f ≫ g) = monMap O f ≫ monMap O g := sorry

/-- The symmetric algebra functor viewed in graded monoid objects. -/
noncomputable def monFunctor :
    ringedSiteModuleCategory J O ⥤ Mon (GradedObject ℕ (ringedSiteModuleCategory J O)) where
  obj := mon O
  map := monMap O
  map_id := monMap_id O
  map_comp := monMap_comp O

/-- The commutative-monoid morphism induced by a module-sheaf morphism. -/
noncomputable def commMonMap {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    commMon O F ⟶ commMon O G :=
  CommMon.homMk (monMap O f)

/-- The degree-`n` component of the underlying commutative symmetric-algebra map. -/
@[simp]
theorem commMonMap_hom_apply
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) (n : ℕ) :
    (commMonMap O f).hom.hom n = map O f n := sorry

/-- The symmetric-algebra commutative-monoid map of an identity is the identity. -/
theorem commMonMap_id (F : ringedSiteModuleCategory J O) :
    commMonMap O (𝟙 F) = 𝟙 (commMon O F) := sorry

/-- Symmetric-algebra commutative-monoid maps preserve composition. -/
theorem commMonMap_comp {F G H : ringedSiteModuleCategory J O}
    (f : F ⟶ G) (g : G ⟶ H) :
    commMonMap O (f ≫ g) = commMonMap O f ≫ commMonMap O g := sorry

/-- The canonical symmetric-algebra functor to graded commutative monoid objects. -/
@[stacks 01CF "graded symmetric-algebra commutative-monoid functor"]
noncomputable def commMonFunctor :
    ringedSiteModuleCategory J O ⥤ CommMon (GradedObject ℕ (ringedSiteModuleCategory J O)) where
  obj := commMon O
  map := commMonMap O
  map_id := commMonMap_id O
  map_comp := commMonMap_comp O

/-- Forgetting commutativity from the symmetric-algebra functor gives its monoid functor. -/
theorem commMonFunctor_comp_forget₂Mon :
    commMonFunctor O ⋙
      CommMon.forget₂Mon (GradedObject ℕ (ringedSiteModuleCategory J O)) =
        monFunctor O := sorry

/-- Forgetting multiplication from the symmetric-algebra monoid functor gives symmetric powers. -/
theorem monFunctor_comp_forget :
    monFunctor O ⋙ Mon.forget (GradedObject ℕ (ringedSiteModuleCategory J O)) =
      gradedObjectFunctor O := sorry

/-- Forgetting all algebra structure from the symmetric algebra gives graded symmetric powers. -/
theorem commMonFunctor_comp_forget :
    commMonFunctor O ⋙ CommMon.forget (GradedObject ℕ (ringedSiteModuleCategory J O)) =
      gradedObjectFunctor O := sorry

end SheafOfModules.RingedSite.SymmetricPower
