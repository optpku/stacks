module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Enveloping
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite

/-!
# Differential Graded Bimodules

Differential graded `(A, B)`-bimodules are modeled canonically as right modules over the
enveloping DGA `A.opposite ⊗[R] B`.  Restriction along the two factor maps recovers the right
`B`-module and the Koszul-twisted left `A`-module without duplicating module or morphism laws.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- Definition 22.28.1 (3) (0FQH): differential graded `(A, B)`-bimodules, modeled as right
modules over the enveloping DGA `A.opposite ⊗[R] B`. -/
@[stacks 0FQH "differential graded bimodule"]
abbrev DifferentialGradedBimodule
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :=
  DifferentialGradedModule.{u, v} (CochainDGAlgebra.enveloping A B)

namespace DifferentialGradedBimodule

variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- Restrict an enveloping-module action to the right factor `B`. -/
@[stacks 0FQH "right-module restriction of a differential graded bimodule"]
abbrev toRightModule (M : DifferentialGradedBimodule A B) :
    DifferentialGradedModule.{u, v} B :=
  (CochainDGAlgebra.Enveloping.rightHom A B).restrictModule M

/-- Restrict an enveloping-module action to the left factor `A.opposite`. -/
@[stacks 0FQH "opposite-left-module restriction of a differential graded bimodule"]
abbrev toOppositeLeftModule (M : DifferentialGradedBimodule A B) :
    DifferentialGradedModule.{u, v} A.opposite :=
  (CochainDGAlgebra.Enveloping.leftHom A B).restrictModule M

/-- Recover the left `A`-module structure from the restricted right `A.opposite`-module. -/
@[stacks 0FQH "left-module structure recovered from a differential graded bimodule"]
abbrev toLeftModule (M : DifferentialGradedBimodule A B) :
    LeftDifferentialGradedModule.{u, v} A :=
  LeftDifferentialGradedModule.unop M.toOppositeLeftModule

/-- The homogeneous right `B`-action of a differential graded bimodule. -/
@[stacks 0FQH "right homogeneous action of a differential graded bimodule"]
abbrev rightMul (M : DifferentialGradedBimodule A B) (p j : ℤ) :
    M.X p →ₗ[R] B.X j →ₗ[R] M.X (p + j) :=
  M.toRightModule.smul p j

/-- The homogeneous left `A`-action of a differential graded bimodule. -/
@[stacks 0FQH "left homogeneous action of a differential graded bimodule"]
abbrev leftMul (M : DifferentialGradedBimodule A B) (i p : ℤ) :
    A.X i →ₗ[R] M.X p →ₗ[R] M.X (i + p) :=
  M.toLeftModule.smul i p

/-- Restriction to the right factor preserves every homogeneous component. -/
@[simp, stacks 0FQH "right restriction preserves graded objects"]
theorem toRightModule_X (M : DifferentialGradedBimodule A B) (n : ℤ) :
    M.toRightModule.X n = M.X n := sorry

/-- Restriction to the right factor preserves the differential. -/
@[simp, stacks 0FQH "right restriction preserves differentials"]
theorem toRightModule_d (M : DifferentialGradedBimodule A B) (n : ℤ) :
    M.toRightModule.d n = M.d n := sorry

/-- Restriction to the right factor evaluates through the canonical factor map. -/
@[simp, stacks 0FQH "right restriction action formula"]
theorem toRightModule_smul (M : DifferentialGradedBimodule A B)
    (p j : ℤ) (x : M.X p) (b : B.X j) :
    M.rightMul p j x b =
      M.smul p j x (CochainDGAlgebra.Enveloping.right A B b) := sorry

/-- Restriction to the opposite left factor preserves every homogeneous component. -/
@[simp, stacks 0FQH "opposite-left restriction preserves graded objects"]
theorem toOppositeLeftModule_X (M : DifferentialGradedBimodule A B) (n : ℤ) :
    M.toOppositeLeftModule.X n = M.X n := sorry

/-- Recovering the left module preserves every homogeneous component. -/
@[simp, stacks 0FQH "left recovery preserves graded objects"]
theorem toLeftModule_X (M : DifferentialGradedBimodule A B) (n : ℤ) :
    M.toLeftModule.X n = M.X n := sorry

/-- Recovering the left module preserves the differential. -/
@[simp, stacks 0FQH "left recovery preserves differentials"]
theorem toLeftModule_d (M : DifferentialGradedBimodule A B) (n : ℤ) :
    M.toLeftModule.d n = M.d n := sorry

/-- The recovered left action is the Koszul-twisted restriction along the left factor. -/
@[simp, stacks 0FQH "left recovered action formula"]
theorem leftMul_apply (M : DifferentialGradedBimodule A B)
    (i p : ℤ) (a : A.X i) (x : M.X p) :
    M.leftMul i p a x =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_comm p i))
        (CochainDGAlgebra.oppositeSign R i p •
          M.smul p i x (CochainDGAlgebra.Enveloping.left A B a)) := sorry

/-- Morphisms of differential graded bimodules are morphisms over the enveloping DGA. -/
@[stacks 0FQH "morphisms of differential graded bimodules"]
abbrev Hom (M N : DifferentialGradedBimodule A B) :=
  DifferentialGradedModule.Hom M N

namespace Hom

/-- Restrict a bimodule morphism to a morphism of right `B`-modules. -/
@[stacks 0FQH "right restriction of a bimodule morphism"]
abbrev toRightHom {M N : DifferentialGradedBimodule A B} (f : Hom M N) :
    DifferentialGradedModule.Hom M.toRightModule N.toRightModule :=
  (CochainDGAlgebra.Enveloping.rightHom A B).restrictHom f

/-- Restrict a bimodule morphism to a morphism of right `A.opposite`-modules. -/
@[stacks 0FQH "opposite-left restriction of a bimodule morphism"]
abbrev toOppositeLeftHom {M N : DifferentialGradedBimodule A B} (f : Hom M N) :
    DifferentialGradedModule.Hom M.toOppositeLeftModule N.toOppositeLeftModule :=
  (CochainDGAlgebra.Enveloping.leftHom A B).restrictHom f

/-- Recover the corresponding morphism of left `A`-modules. -/
@[stacks 0FQH "left restriction of a bimodule morphism"]
abbrev toLeftHom {M N : DifferentialGradedBimodule A B} (f : Hom M N) :
    LeftDifferentialGradedModule.Hom M.toLeftModule N.toLeftModule :=
  LeftDifferentialGradedModule.Hom.unop
    ((CochainDGAlgebra.Enveloping.leftHom A B).restrictHom f)

/-- The identity morphism of a differential graded bimodule. -/
@[stacks 0FQH "identity of differential graded bimodules"]
abbrev id (M : DifferentialGradedBimodule A B) : Hom M M :=
  DifferentialGradedModule.Hom.id M

/-- Composition of differential graded bimodule morphisms. -/
@[stacks 0FQH "composition of differential graded bimodule morphisms"]
abbrev comp {L M N : DifferentialGradedBimodule A B}
    (g : Hom M N) (f : Hom L M) : Hom L N :=
  DifferentialGradedModule.Hom.comp g f

/-- Restricting a morphism to the right factor preserves every degreewise component. -/
@[simp, stacks 0FQH "right restricted morphism components"]
theorem toRightHom_hom {M N : DifferentialGradedBimodule A B}
    (f : Hom M N) (n : ℤ) :
    (toRightHom f).hom n = f.hom n := sorry

/-- Restricting a morphism to the left module preserves every degreewise component. -/
@[simp, stacks 0FQH "left restricted morphism components"]
theorem toLeftHom_hom {M N : DifferentialGradedBimodule A B}
    (f : Hom M N) (n : ℤ) :
    (toLeftHom f).hom n = f.hom n := sorry

end Hom

/-- Evaluation of an enveloping-module morphism agrees with its restricted right-module map. -/
@[simp, stacks 0FQH "bimodule morphism evaluation through right restriction"]
theorem hom_coe_apply {M N : DifferentialGradedBimodule A B}
    (f : Hom M N) (n : ℤ) (x : M.X n) :
    f n x = Hom.toRightHom f n x := sorry

/-- Restriction of scalars from the enveloping DGA to the right factor. -/
@[stacks 0FQH "right restriction functor for differential graded bimodules"]
abbrev forgetToRightModule (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    DifferentialGradedBimodule A B ⥤ DifferentialGradedModule.{u, v} B :=
  (CochainDGAlgebra.Enveloping.rightHom A B).restrictFunctor

/-- Restriction of scalars from the enveloping DGA to the opposite left factor. -/
@[stacks 0FQH "opposite-left restriction functor for differential graded bimodules"]
abbrev forgetToOppositeLeftModule (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    DifferentialGradedBimodule A B ⥤
      DifferentialGradedModule.{u, v} A.opposite :=
  (CochainDGAlgebra.Enveloping.leftHom A B).restrictFunctor

/-- The functor recovering the left `A`-module underlying a differential graded bimodule. -/
@[stacks 0FQH "left restriction functor for differential graded bimodules"]
abbrev forgetToLeftModule (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    DifferentialGradedBimodule A B ⥤ LeftDifferentialGradedModule.{u, v} A :=
  (CochainDGAlgebra.Enveloping.leftHom A B).restrictFunctor ⋙
    LeftDifferentialGradedModule.unopFunctor A

/-- The right-module restriction functor has the expected object map. -/
@[simp, stacks 0FQH "right restriction functor on objects"]
theorem forgetToRightModule_obj (M : DifferentialGradedBimodule A B) :
    (forgetToRightModule A B).obj M = M.toRightModule := sorry

/-- The right-module restriction functor has the expected morphism map. -/
@[simp, stacks 0FQH "right restriction functor on morphisms"]
theorem forgetToRightModule_map {M N : DifferentialGradedBimodule A B} (f : M ⟶ N) :
    (forgetToRightModule A B).map f = Hom.toRightHom f := sorry

/-- The left-module restriction functor has the expected object map. -/
@[simp, stacks 0FQH "left restriction functor on objects"]
theorem forgetToLeftModule_obj (M : DifferentialGradedBimodule A B) :
    (forgetToLeftModule A B).obj M = M.toLeftModule := sorry

/-- The left-module restriction functor has the expected morphism map. -/
@[simp, stacks 0FQH "left restriction functor on morphisms"]
theorem forgetToLeftModule_map {M N : DifferentialGradedBimodule A B} (f : M ⟶ N) :
    (forgetToLeftModule A B).map f = Hom.toLeftHom f := sorry

/-- Restriction to the right factor is faithful. -/
@[stacks 0FQH "faithfulness of right restriction"]
instance forgetToRightModule_faithful (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    Functor.Faithful (forgetToRightModule.{u, v} A B) := sorry

/-- Restriction to the left factor is faithful. -/
@[stacks 0FQH "faithfulness of left restriction"]
instance forgetToLeftModule_faithful (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) :
    Functor.Faithful (forgetToLeftModule.{u, v} A B) := sorry

end DifferentialGradedBimodule
