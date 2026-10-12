/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.NatMonoidal
public import ReasLib.CategoryTheory.GradedObject.Monoid
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded tensor algebra as a monoid object

Tensor powers, their concatenation maps, and the degree-zero unit assemble into a canonical
monoid object in Mathlib's category of naturally graded module sheaves.  The construction is
functorial in the module sheaf and retains an independent coefficient universe.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

/-- The naturally graded object whose degree `n` is the tensor-power sheaf
`SheafOfModules.RingedSite.TensorPower.sheaf O F n`. -/
@[stacks 01CF "graded object of tensor powers"]
noncomputable abbrev gradedObject
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  sheaf O F

/-- The homogeneous degree-zero unit of the graded tensor-power object. -/
@[stacks 01CF "unit of the graded tensor monoid"]
noncomputable def gradedOne
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    𝟙_ (ringedSiteModuleCategory.{u, v, w, w} J O) ⟶ gradedObject O F 0 :=
  (unitIsoTensorUnit (J := J) (𝒪 := O)).inv ≫ one O F

/-- Multiplication between two homogeneous components of the graded tensor-power object. -/
@[stacks 01CF "homogeneous multiplication of the graded tensor monoid"]
noncomputable def gradedMul
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) (n m : ℕ) :
    MonoidalCategory.tensorObj (gradedObject O F n) (gradedObject O F m) ⟶
      gradedObject O F (n + m) :=
  mul O F n m

/-- The assembled unit morphism of the naturally graded tensor-power object. -/
noncomputable def oneHom
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    𝟙_ (GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O)) ⟶
      gradedObject O F :=
  GradedObject.Monoidal.oneHom (gradedObject O F) (gradedOne O F)

/-- The assembled multiplication morphism of the naturally graded tensor-power object. -/
noncomputable def mulHom
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    gradedObject O F ⊗ gradedObject O F ⟶ gradedObject O F :=
  GradedObject.Monoidal.mulHom (gradedObject O F) (gradedMul O F)

/-- The assembled tensor-power unit is a left identity. -/
theorem oneHom_mulHom
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    oneHom O F ▷ gradedObject O F ≫ mulHom O F =
      (λ_ (gradedObject O F)).hom := sorry

/-- The assembled tensor-power unit is a right identity. -/
theorem mulHom_oneHom
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    gradedObject O F ◁ oneHom O F ≫ mulHom O F =
      (ρ_ (gradedObject O F)).hom := sorry

/-- The assembled tensor-power multiplication is associative. -/
theorem mulHom_assoc
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    (mulHom O F ▷ gradedObject O F) ≫ mulHom O F =
      (α_ (gradedObject O F) (gradedObject O F) (gradedObject O F)).hom ≫
        (gradedObject O F ◁ mulHom O F) ≫ mulHom O F := sorry

/-- The canonical monoid-object structure on the naturally graded tensor powers. -/
@[stacks 01CF "graded tensor monoid object", implicit_reducible]
noncomputable def monObj
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    MonObj (gradedObject O F) :=
  GradedObject.Monoidal.monObj (gradedObject O F) (gradedOne O F) (gradedMul O F)
    (oneHom_mulHom O F) (mulHom_oneHom O F) (mulHom_assoc O F)

/-- The tensor algebra bundled in Mathlib's category of graded monoid objects. -/
@[stacks 01CF "bundled graded tensor algebra", implicit_reducible]
noncomputable def mon
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    Mon (GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O)) :=
  GradedObject.Monoidal.mon (gradedObject O F) (gradedOne O F) (gradedMul O F)
    (oneHom_mulHom O F) (mulHom_oneHom O F) (mulHom_assoc O F)

/-- The underlying graded object of the bundled tensor algebra is its tensor-power family. -/
@[simp]
theorem mon_X
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    (mon O F).X = gradedObject O F := sorry

/-- The bundled tensor-algebra unit is the unit assembled from degree zero. -/
@[simp]
theorem mon_one
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    η[(mon O F).X] = oneHom O F := sorry

/-- The bundled tensor-algebra multiplication is assembled from homogeneous concatenation. -/
@[simp]
theorem mon_mul
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    μ[(mon O F).X] = mulHom O F := sorry

/-- On degrees `(n, m)`, bundled tensor-algebra multiplication is canonical concatenation. -/
@[reassoc (attr := simp)]
theorem ι_mon_mul_add
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) (n m : ℕ) :
    GradedObject.Monoidal.ιTensorObj (gradedObject O F) (gradedObject O F)
        n m (n + m) rfl ≫ μ[(mon O F).X] (n + m) = gradedMul O F n m := sorry

/-- The morphism of graded tensor-power objects induced by a module-sheaf morphism. -/
@[stacks 01CF "map of graded tensor-power objects"]
noncomputable def mapHom
    {F G : ringedSiteModuleCategory.{u, v, w, w} J O} (f : F ⟶ G) :
    gradedObject O F ⟶ gradedObject O G :=
  fun n ↦ map O f n

/-- The degree-`n` component of the induced graded tensor-power morphism. -/
@[simp, stacks 01CF "component of a graded tensor-power map"]
theorem mapHom_apply
    {F G : ringedSiteModuleCategory.{u, v, w, w} J O} (f : F ⟶ G) (n : ℕ) :
    mapHom O f n = map O f n := sorry

/-- The induced graded tensor-power morphism preserves identity morphisms. -/
@[stacks 01CF "identity law for graded tensor-power maps"]
theorem mapHom_id
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    mapHom O (𝟙 F) = 𝟙 (gradedObject O F) := sorry

/-- The induced graded tensor-power morphism preserves composition. -/
@[stacks 01CF "composition law for graded tensor-power maps"]
theorem mapHom_comp
    {F G H : ringedSiteModuleCategory.{u, v, w, w} J O}
    (f : F ⟶ G) (g : G ⟶ H) :
    mapHom O (f ≫ g) = mapHom O f ≫ mapHom O g := sorry

/-- Tensor powers as a functor to naturally graded module sheaves. -/
@[stacks 01CF "graded tensor-power functor"]
noncomputable def gradedObjectFunctor :
    ringedSiteModuleCategory.{u, v, w, w} J O ⥤
      GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O) where
  obj := gradedObject O
  map := mapHom O
  map_id := mapHom_id O
  map_comp := mapHom_comp O

/-- The induced graded tensor-power morphism preserves the assembled unit. -/
@[stacks 01CF "unit preservation for graded tensor-power maps"]
theorem mapHom_one
    {F G : ringedSiteModuleCategory.{u, v, w, w} J O} (f : F ⟶ G) :
    oneHom O F ≫ mapHom O f = oneHom O G := sorry

/-- The induced graded tensor-power morphism preserves the assembled multiplication. -/
@[stacks 01CF "multiplication preservation for graded tensor-power maps"]
theorem mapHom_mul
    {F G : ringedSiteModuleCategory.{u, v, w, w} J O} (f : F ⟶ G) :
    mulHom O F ≫ mapHom O f =
      (mapHom O f ⊗ₘ mapHom O f) ≫ mulHom O G := sorry

/-- The monoid-object morphism induced by a module-sheaf morphism. -/
@[stacks 01CF "map of graded tensor-algebra monoid objects"]
noncomputable def monMap
    {F G : ringedSiteModuleCategory.{u, v, w, w} J O} (f : F ⟶ G) :
    mon O F ⟶ mon O G :=
  Mon.Hom.mk' (mapHom O f) (mapHom_one O f) (mapHom_mul O f)

/-- The degree-`n` component of the underlying morphism of a tensor-algebra map. -/
@[simp, stacks 01CF "component of a graded tensor-algebra map"]
theorem monMap_hom_apply
    {F G : ringedSiteModuleCategory.{u, v, w, w} J O} (f : F ⟶ G) (n : ℕ) :
    (monMap O f).hom n = map O f n := sorry

/-- The tensor-algebra monoid map associated to an identity is the identity. -/
@[stacks 01CF "identity law for graded tensor-algebra maps"]
theorem monMap_id
    (F : ringedSiteModuleCategory.{u, v, w, w} J O) :
    monMap O (𝟙 F) = 𝟙 (mon O F) := sorry

/-- Tensor-algebra monoid maps preserve composition. -/
@[stacks 01CF "composition law for graded tensor-algebra maps"]
theorem monMap_comp
    {F G H : ringedSiteModuleCategory.{u, v, w, w} J O}
    (f : F ⟶ G) (g : G ⟶ H) :
    monMap O (f ≫ g) = monMap O f ≫ monMap O g := sorry

/-- The canonical tensor-algebra functor to graded monoid objects. -/
@[stacks 01CF "graded tensor-algebra monoid functor"]
noncomputable def monFunctor :
    ringedSiteModuleCategory.{u, v, w, w} J O ⥤
      Mon (GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O)) where
  obj := mon O
  map := monMap O
  map_id := monMap_id O
  map_comp := monMap_comp O

/-- Forgetting multiplication from the tensor-algebra functor recovers graded tensor powers. -/
@[stacks 01CF "underlying graded-object functor of the tensor algebra"]
theorem monFunctor_comp_forget :
    monFunctor O ⋙ Mon.forget
      (GradedObject ℕ (ringedSiteModuleCategory.{u, v, w, w} J O)) =
        gradedObjectFunctor O := sorry

end SheafOfModules.RingedSite.TensorPower
