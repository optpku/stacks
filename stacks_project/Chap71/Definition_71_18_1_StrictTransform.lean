module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap70.Lemma_70_14_5_SectionsWithSupport
public import stacks_project.Chap71.Lemma_71_6_12_Pullback

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteType

/-!
# Strict transforms of modules and algebraic spaces

The shared strict-transform constructions specialize to an exceptional inverse image
when the base morphism is a blowup. The foundational imports retain the inverse-image
and subspace interfaces used by existing consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure sheaf of an algebraic space, viewed as a module over itself, is
quasi-coherent. -/
abbrev instIsQuasicoherent_structureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsQuasicoherent :=
  AlgebraicGeometry.AlgebraicSpace.Modules.instIsQuasicoherentUnit X

end AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
variable (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B) (F : X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.strictTransformModule b E f F :
  (strictTransformAmbient b f).Modules)

section
variable [QuasiCompact (strictTransformOpenComplement b E f).ι]

#check (AlgebraicGeometry.AlgebraicSpace.strictTransform b E f :
  ClosedSubspace (strictTransformAmbient b f))

end
