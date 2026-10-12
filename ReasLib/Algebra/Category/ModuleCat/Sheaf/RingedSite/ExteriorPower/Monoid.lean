/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.NatMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.GradedObject.Monoid
import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded exterior algebra as a monoid object

The exterior-power sheaves and their fixed-degree multiplication are assembled into Mathlib's
canonical monoid-object category of naturally graded module sheaves.  This is the categorical
owner; sectionwise graded-algebra structures are derived or compatibility-facing presentations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The naturally graded object whose degree `n` is the exterior-power sheaf `Λ^n(F)`. -/
@[stacks 01CF "graded object of exterior powers"]
noncomputable abbrev gradedObject (F : ringedSiteModuleCategory J 𝒪) :
    GradedObject ℕ (ringedSiteModuleCategory J 𝒪) :=
  sheaf 𝒪 F

/-- The homogeneous degree-zero unit, with the structure module identified with the categorical
tensor unit. -/
@[stacks 01CF "unit of the graded exterior monoid"]
noncomputable def gradedOne (F : ringedSiteModuleCategory J 𝒪) :
    𝟙_ (ringedSiteModuleCategory J 𝒪) ⟶ gradedObject 𝒪 F 0 :=
  (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv ≫ one 𝒪 F

/-- Multiplication between two homogeneous components of the graded exterior object. -/
@[stacks 01CF "homogeneous multiplication of the graded exterior monoid"]
noncomputable def gradedMul (F : ringedSiteModuleCategory J 𝒪) (n m : ℕ) :
    MonoidalCategory.tensorObj (gradedObject 𝒪 F n) (gradedObject 𝒪 F m) ⟶
      gradedObject 𝒪 F (n + m) :=
  mul 𝒪 F n m

/-- The assembled unit morphism of the naturally graded exterior object. -/
noncomputable def oneHom (F : ringedSiteModuleCategory J 𝒪) :
    𝟙_ (GradedObject ℕ (ringedSiteModuleCategory J 𝒪)) ⟶ gradedObject 𝒪 F :=
  GradedObject.Monoidal.oneHom (gradedObject 𝒪 F) (gradedOne 𝒪 F)

/-- The assembled multiplication morphism of the naturally graded exterior object. -/
noncomputable def mulHom (F : ringedSiteModuleCategory J 𝒪) :
    gradedObject 𝒪 F ⊗ gradedObject 𝒪 F ⟶ gradedObject 𝒪 F :=
  GradedObject.Monoidal.mulHom (gradedObject 𝒪 F) (gradedMul 𝒪 F)

/-- The assembled exterior unit is a left identity. -/
theorem oneHom_mulHom (F : ringedSiteModuleCategory J 𝒪) :
    oneHom 𝒪 F ▷ gradedObject 𝒪 F ≫ mulHom 𝒪 F =
      (λ_ (gradedObject 𝒪 F)).hom := sorry

/-- The assembled exterior unit is a right identity. -/
theorem mulHom_oneHom (F : ringedSiteModuleCategory J 𝒪) :
    gradedObject 𝒪 F ◁ oneHom 𝒪 F ≫ mulHom 𝒪 F =
      (ρ_ (gradedObject 𝒪 F)).hom := sorry

/-- The assembled exterior multiplication is associative. -/
theorem mulHom_assoc (F : ringedSiteModuleCategory J 𝒪) :
    (mulHom 𝒪 F ▷ gradedObject 𝒪 F) ≫ mulHom 𝒪 F =
      (α_ (gradedObject 𝒪 F) (gradedObject 𝒪 F) (gradedObject 𝒪 F)).hom ≫
        (gradedObject 𝒪 F ◁ mulHom 𝒪 F) ≫ mulHom 𝒪 F := sorry

/-- The canonical monoid-object structure on the naturally graded exterior powers. -/
@[stacks 01CF "graded exterior monoid object", implicit_reducible]
noncomputable def monObj (F : ringedSiteModuleCategory J 𝒪) :
    MonObj (gradedObject 𝒪 F) :=
  GradedObject.Monoidal.monObj (gradedObject 𝒪 F) (gradedOne 𝒪 F) (gradedMul 𝒪 F)
    (oneHom_mulHom 𝒪 F) (mulHom_oneHom 𝒪 F) (mulHom_assoc 𝒪 F)

/-- The graded exterior algebra bundled in Mathlib's category of monoid objects. -/
@[stacks 01CF "bundled graded exterior algebra", implicit_reducible]
noncomputable def mon (F : ringedSiteModuleCategory J 𝒪) :
    Mon (GradedObject ℕ (ringedSiteModuleCategory J 𝒪)) :=
  GradedObject.Monoidal.mon (gradedObject 𝒪 F) (gradedOne 𝒪 F) (gradedMul 𝒪 F)
    (oneHom_mulHom 𝒪 F) (mulHom_oneHom 𝒪 F) (mulHom_assoc 𝒪 F)

/-- The underlying graded object of the bundled exterior algebra is the exterior-power family. -/
@[simp]
theorem mon_X (F : ringedSiteModuleCategory J 𝒪) :
    (mon 𝒪 F).X = gradedObject 𝒪 F := sorry

/-- The unit of the bundled exterior algebra is the assembled degree-zero exterior unit. -/
@[simp]
theorem mon_one (F : ringedSiteModuleCategory J 𝒪) :
    η[(mon 𝒪 F).X] = oneHom 𝒪 F := sorry

/-- The multiplication of the bundled exterior algebra is assembled from the fixed-degree
exterior multiplication maps. -/
@[simp]
theorem mon_mul (F : ringedSiteModuleCategory J 𝒪) :
    μ[(mon 𝒪 F).X] = mulHom 𝒪 F := sorry

/-- On the summand of degrees `(n, m)`, bundled exterior multiplication is the canonical
fixed-degree exterior multiplication. -/
@[reassoc (attr := simp)]
theorem ι_mon_mul_add (F : ringedSiteModuleCategory J 𝒪) (n m : ℕ) :
    GradedObject.Monoidal.ιTensorObj (gradedObject 𝒪 F) (gradedObject 𝒪 F)
        n m (n + m) rfl ≫ μ[(mon 𝒪 F).X] (n + m) = gradedMul 𝒪 F n m := sorry

/-- The morphism of graded exterior-power objects induced by a module-sheaf morphism. -/
noncomputable def mapHom {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    gradedObject 𝒪 F ⟶ gradedObject 𝒪 G :=
  fun n ↦ map 𝒪 f n

/-- The degree-`n` component of the induced graded exterior-power morphism. -/
@[simp]
theorem mapHom_apply {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (n : ℕ) :
    mapHom 𝒪 f n = map 𝒪 f n := sorry

/-- The induced graded exterior-power morphism preserves identity morphisms. -/
theorem mapHom_id (F : ringedSiteModuleCategory J 𝒪) :
    mapHom 𝒪 (𝟙 F) = 𝟙 (gradedObject 𝒪 F) := sorry

/-- The induced graded exterior-power morphism preserves composition. -/
theorem mapHom_comp {F G H : ringedSiteModuleCategory J 𝒪}
    (f : F ⟶ G) (g : G ⟶ H) :
    mapHom 𝒪 (f ≫ g) = mapHom 𝒪 f ≫ mapHom 𝒪 g := sorry

/-- Exterior powers as a functor to naturally graded module sheaves. -/
@[stacks 01CF "graded exterior-power functor"]
noncomputable def gradedObjectFunctor :
    ringedSiteModuleCategory J 𝒪 ⥤ GradedObject ℕ (ringedSiteModuleCategory J 𝒪) where
  obj := gradedObject 𝒪
  map := mapHom 𝒪
  map_id := mapHom_id 𝒪
  map_comp := mapHom_comp 𝒪

/-- The induced graded exterior-power morphism preserves the assembled unit. -/
theorem mapHom_one {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    oneHom 𝒪 F ≫ mapHom 𝒪 f = oneHom 𝒪 G := sorry

/-- The induced graded exterior-power morphism preserves the assembled multiplication. -/
theorem mapHom_mul {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    mulHom 𝒪 F ≫ mapHom 𝒪 f =
      (mapHom 𝒪 f ⊗ₘ mapHom 𝒪 f) ≫ mulHom 𝒪 G := sorry

/-- The exterior-algebra monoid morphism induced by a module-sheaf morphism. -/
noncomputable def monMap {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    mon 𝒪 F ⟶ mon 𝒪 G :=
  Mon.Hom.mk' (mapHom 𝒪 f) (mapHom_one 𝒪 f) (mapHom_mul 𝒪 f)

/-- The degree-`n` component of the underlying exterior-algebra morphism. -/
@[simp]
theorem monMap_hom_apply
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (n : ℕ) :
    (monMap 𝒪 f).hom n = map 𝒪 f n := sorry

/-- The exterior-algebra monoid map associated to an identity is the identity. -/
theorem monMap_id (F : ringedSiteModuleCategory J 𝒪) :
    monMap 𝒪 (𝟙 F) = 𝟙 (mon 𝒪 F) := sorry

/-- Exterior-algebra monoid maps preserve composition. -/
theorem monMap_comp {F G H : ringedSiteModuleCategory J 𝒪}
    (f : F ⟶ G) (g : G ⟶ H) :
    monMap 𝒪 (f ≫ g) = monMap 𝒪 f ≫ monMap 𝒪 g := sorry

/-- The canonical exterior-algebra functor to graded monoid objects. -/
@[stacks 01CF "graded exterior-algebra monoid functor"]
noncomputable def monFunctor :
    ringedSiteModuleCategory J 𝒪 ⥤
      Mon (GradedObject ℕ (ringedSiteModuleCategory J 𝒪)) where
  obj := mon 𝒪
  map := monMap 𝒪
  map_id := monMap_id 𝒪
  map_comp := monMap_comp 𝒪

/-- Forgetting multiplication from the exterior-algebra functor recovers exterior powers. -/
theorem monFunctor_comp_forget :
    monFunctor 𝒪 ⋙ Mon.forget (GradedObject ℕ (ringedSiteModuleCategory J 𝒪)) =
      gradedObjectFunctor 𝒪 := sorry

end SheafOfModules.RingedSite.ExteriorPower

