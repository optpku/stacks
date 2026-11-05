module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Center.Linear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base-ring linearity for module sheaves

If `O` is a sheaf of commutative `R`-algebras, its module sheaves are canonically
`R`-linear.  The action is built through the categorical center, so it is compatible
with restriction maps and does not install a competing global scalar instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe r u v w z

namespace SheafOfModules.CommAlg

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Sheaves of modules over the underlying ring sheaf of a sheaf of commutative `R`-algebras. -/
@[stacks 0CS6 "module sheaves over a commutative algebra sheaf"]
abbrev Modules (O : Sheaf J (CommAlgCat.{w} R)) :=
  SheafOfModules.{z} (CategoryTheory.Sheaf.CommAlg.ring O)

/-- The module-sheaf carrier has a direct zero-object owner.  Keeping this bridge next to
`Modules` avoids selecting an Abelian transfer instance at a different universe level in
homotopy and derived constructions. -/
@[stacks 0CS6 "zero object of module sheaves over a commutative algebra sheaf"]
noncomputable instance modulesHasZeroObject (O : Sheaf J (CommAlgCat.{w} R)) :
    HasZeroObject (Modules O) :=
  SheafOfModules.instHasZeroObject

variable (O : Sheaf J (CommAlgCat.{w} R))

/-- The base-ring map into the underlying local ring at an object of the site. -/
@[stacks 0CS6 "base ring map at a site object"]
def baseRingHom (U : Cᵒᵖ) :
    R →+* (CategoryTheory.Sheaf.CommAlg.ring O).obj.obj U :=
  algebraMap R (O.obj.obj U)

/-- The image of the base ring lies in the center of every underlying local ring. -/
@[stacks 0CS6 "centrality of the base ring image"]
theorem baseRingHom_comm (U : Cᵒᵖ) (r : R)
    (a : (CategoryTheory.Sheaf.CommAlg.ring O).obj.obj U) :
    baseRingHom O U r * a = a * baseRingHom O U r := sorry

/-- The base-ring maps commute with restriction in the algebra sheaf. -/
@[stacks 0CS6 "naturality of the base ring map", simp]
theorem map_baseRingHom {U V : Cᵒᵖ} (f : U ⟶ V) (r : R) :
    ((CategoryTheory.Sheaf.CommAlg.ring O).obj.map f).hom (baseRingHom O U r) =
      baseRingHom O V r := sorry

/-- Multiplication by a base-ring scalar as a linear map over the underlying local ring. -/
@[stacks 0CS6 "objectwise base scalar map"]
noncomputable def scalarLinearMap (M : Modules O) (r : R) (U : Cᵒᵖ) :
    M.val.obj U →ₗ[(CategoryTheory.Sheaf.CommAlg.ring O).obj.obj U] M.val.obj U where
  toFun x := baseRingHom O U r • x
  map_add' := sorry
  map_smul' := sorry

/-- Evaluation of the objectwise base scalar map. -/
@[stacks 0CS6 "evaluation of the objectwise base scalar map", simp]
theorem scalarLinearMap_apply (M : Modules O) (r : R) (U : Cᵒᵖ) (x : M.val.obj U) :
    scalarLinearMap O M r U x = baseRingHom O U r • x := sorry

/-- Objectwise multiplication by a base-ring scalar. -/
@[stacks 0CS6 "objectwise scalar morphism"]
noncomputable def scalarApp (M : Modules O) (r : R) (U : Cᵒᵖ) :
    M.val.obj U ⟶ M.val.obj U :=
  ModuleCat.ofHom (scalarLinearMap O M r U)

/-- Evaluation of the objectwise scalar morphism. -/
@[stacks 0CS6 "evaluation of the objectwise scalar morphism", simp]
theorem scalarApp_apply (M : Modules O) (r : R) (U : Cᵒᵖ) (x : M.val.obj U) :
    scalarApp O M r U x = baseRingHom O U r • x := sorry

/-- Objectwise base-ring scalar multiplication commutes with restriction. -/
@[reassoc, stacks 0CS6 "naturality of objectwise scalar morphisms"]
theorem scalarApp_naturality (M : Modules O) (r : R)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    M.val.map f ≫
        (ModuleCat.restrictScalars
          ((CategoryTheory.Sheaf.CommAlg.ring O).obj.map f).hom).map
          (scalarApp O M r V) =
      scalarApp O M r U ≫ M.val.map f := sorry

/-- Multiplication by a base-ring scalar as an endomorphism of a module sheaf. -/
@[stacks 0CS6 "scalar endomorphism of a module sheaf"]
noncomputable def scalar (M : Modules O) (r : R) : M ⟶ M where
  val :=
    { app := scalarApp O M r
      naturality := scalarApp_naturality O M r }

/-- Base-ring scalars act on module sheaves through the categorical center. -/
@[stacks 0CS6 "base ring action through the categorical center"]
noncomputable def centerHom : R →+* CatCenter (Modules O) where
  toFun r :=
    { app := fun M => scalar O M r
      naturality := sorry }
  map_one' := sorry
  map_zero' := sorry
  map_mul' := sorry
  map_add' := sorry

/-- The scalar endomorphism of one module sheaf, exposed as a ring homomorphism. -/
@[stacks 0CS6 "scalar endomorphism ring homomorphism"]
noncomputable def scalarHom (M : Modules O) : R →+* End M where
  toFun r := scalar O M r
  map_one' := sorry
  map_zero' := sorry
  map_mul' := sorry
  map_add' := sorry

/-- Evaluating the center action at a module sheaf gives its scalar endomorphism. -/
@[stacks 0CS6 "evaluation of the categorical-center scalar action", simp]
theorem centerHom_app (M : Modules O) (r : R) :
    (centerHom O r).app M = scalar O M r := sorry

/-- The module structure on a hom induced by the categorical-center action. -/
@[stacks 0CS6 "base-ring module structure on module-sheaf morphisms", implicit_reducible]
noncomputable def homModuleDef (M N : Modules O) : Module R (M ⟶ N) :=
  CategoryTheory.Linear.homModuleOfRingMorphism (centerHom O) M N

/-- Module sheaves over an `R`-algebra sheaf form an `R`-linear category.

The instance is scoped so that it does not alter unrelated ambient categories; consumers opt in
with `open scoped SheafOfModules.CommAlg`. -/
@[stacks 0CS6 "scoped base-ring linearity of module sheaves"]
noncomputable scoped instance (priority := 1100) linear : Linear R (Modules O) :=
  CategoryTheory.Linear.ofRingMorphism (centerHom O)

section Integral

variable {C₀ : Type u} [Category.{v} C₀]
variable {J₀ : GrothendieckTopology C₀}
variable [J₀.HasSheafCompose (forget₂ (CommAlgCat.{w} ℤ) CommRingCat.{w})]
variable [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O₀ : Sheaf J₀ (CommAlgCat.{w} ℤ))

/-- The integral scalar action selected inside the commutative-algebra-sheaf scope. -/
@[stacks 0CS6 "scoped integral scalar action on module-sheaf morphisms"]
noncomputable scoped instance (priority := 1100) intHomSMul
    (M N : Modules O₀) : SMul ℤ (M ⟶ N) :=
  CategoryTheory.Linear.smulOfRingMorphism (centerHom O₀) M N

/-- The integral hom-module instance selected inside the commutative-algebra-sheaf scope. -/
@[stacks 0CS6 "scoped integral module structure on module-sheaf morphisms"]
noncomputable scoped instance (priority := 1100) intHomModule
    (M N : Modules O₀) : Module ℤ (M ⟶ N) :=
  homModuleDef O₀ M N

/-- The integral specialization of base-ring linearity.

Its exact `ℤ` head keeps the opted-in scalar action coherent with `intHomSMul` instead of the
generic preadditive integer action chosen by typeclass specificity. -/
@[stacks 0CS6 "scoped integral linearity of module sheaves"]
noncomputable scoped instance (priority := 1100) intLinear : Linear ℤ (Modules O₀) :=
  linear (R := ℤ) O₀

end Integral

open scoped SheafOfModules.CommAlg

/-- The component of a scalar endomorphism is the objectwise scalar morphism. -/
@[stacks 0CS6 "component of a scalar endomorphism", simp]
theorem scalarHom_app (M : Modules O) (r : R) (U : Cᵒᵖ) :
    (scalarHom O M r).val.app U = scalarApp O M r U := sorry

/-- Evaluation of the base-ring scalar action is objectwise scalar multiplication. -/
@[stacks 0CS6 "objectwise scalar evaluation", simp]
theorem scalarHom_app_apply (M : Modules O) (r : R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((scalarHom O M r).val.app U) x = baseRingHom O U r • x := sorry

/-- A base scalar may act on either side of a module-sheaf morphism. -/
@[reassoc, stacks 0CS6 "central scalar action on module-sheaf morphisms"]
theorem scalar_comp {M N : Modules O} (r : R) (f : M ⟶ N) :
    scalarHom O M r ≫ f = f ≫ scalarHom O N r := sorry

/-- Scalar multiplication of a morphism is composition with its source scalar endomorphism. -/
@[stacks 0CS6 "scalar multiplication as composition"]
theorem smul_eq {M N : Modules O} (r : R) (f : M ⟶ N) :
    r • f = scalarHom O M r ≫ f := sorry

/-- Scalar multiplication of a morphism is computed objectwise. -/
@[stacks 0CS6 "objectwise scalar action on morphisms", simp]
theorem smul_app {M N : Modules O} (r : R) (f : M ⟶ N) (U : Cᵒᵖ) :
    (r • f).val.app U = scalarApp O M r U ≫ f.val.app U := sorry

/-- Scalar multiplication of a morphism is objectwise scalar multiplication. -/
@[stacks 0CS6 "objectwise scalar action on morphisms", simp]
theorem smul_app_apply {M N : Modules O} (r : R) (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((r • f).val.app U) x = baseRingHom O U r • f.val.app U x := sorry

end SheafOfModules.CommAlg
