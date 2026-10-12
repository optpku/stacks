/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.Bimodule

/-!
# The category of graded bimodules

Morphisms of graded bimodules are degree-zero morphisms of the underlying right graded modules
which commute with the left action.  This file supplies the category, its preadditive and linear
structures, and the faithful forgetful functor to degree-zero right graded modules.
-/

@[expose] public section

noncomputable section

universe x y w v u

open CategoryTheory

namespace GradedModule.Bimodule

variable {ι : Type x} [DecidableEq ι] [AddCommMonoid ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ι → Submodule R B} [GradedAlgebra 𝒝]

/-- Degree-zero right graded-module morphisms commuting with the left action form a submodule. -/
def homSubmodule (M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    Submodule R (Right.HomogeneousMap M.toRight N.toRight 0) where
  carrier := {f | ∀ a : A, ∀ x : M,
    f.1 (M.leftAction a x) = N.leftAction a (f.1 x)}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- A morphism of graded bimodules is a degree-zero right graded-module morphism which commutes
with the left action. -/
@[stacks 0FQH "morphisms of graded bimodules"]
abbrev Hom (M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝) : Type _ :=
  homSubmodule M N

namespace Hom

/-- The underlying degree-zero morphism of right graded modules. -/
def toRightHom {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : Hom M N) :
    Right.HomogeneousMap M.toRight N.toRight 0 :=
  f.1

/-- The underlying right-linear map of a graded bimodule morphism. -/
def toLinearMap {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : Hom M N) :
    M →ₗ[Bᵐᵒᵖ] N :=
  (toRightHom f).1

/-- A graded bimodule morphism preserves every homogeneous piece. -/
theorem map_mem {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : Hom M N)
    {i : ι} {x : M} (hx : x ∈ M.grading i) : toLinearMap f x ∈ N.grading i := sorry

/-- A graded bimodule morphism commutes with the left action. -/
@[simp]
theorem map_leftAction {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : Hom M N) (a : A) (x : M) :
    toLinearMap f (M.leftAction a x) = N.leftAction a (toLinearMap f x) := sorry

/-- A graded bimodule morphism commutes with the right action. -/
@[simp]
theorem map_rightAction {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : Hom M N) (x : M) (b : B) :
    toLinearMap f (M.rightAction x b) = N.rightAction (toLinearMap f x) b := sorry

/-- The identity morphism of a graded bimodule. -/
def id (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) : Hom M M :=
  ⟨Right.HomogeneousMap.id M.toRight, sorry⟩

/-- Composition of graded bimodule morphisms. -/
def comp {L M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (g : Hom M N) (f : Hom L M) :
    Hom L N :=
  ⟨⟨(toLinearMap g).comp (toLinearMap f), sorry⟩, sorry⟩

/-- The underlying degree-zero right-module morphism of the identity is the identity. -/
@[simp]
theorem id_toRightHom (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    toRightHom (id M) = Right.HomogeneousMap.id M.toRight := sorry

/-- The underlying right-linear map of a composite is the composite of the underlying maps. -/
@[simp]
theorem comp_toLinearMap {L M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (g : Hom M N) (f : Hom L M) :
    toLinearMap (comp g f) = (toLinearMap g).comp (toLinearMap f) := sorry

/-- The underlying degree-zero map of the zero morphism is zero. -/
@[simp]
theorem zero_toRightHom (M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    toRightHom (0 : Hom M N) = 0 := sorry

/-- The underlying degree-zero map of a sum is the sum of the underlying maps. -/
@[simp]
theorem add_toRightHom {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f g : Hom M N) :
    toRightHom (f + g) = toRightHom f + toRightHom g := sorry

/-- The underlying degree-zero map of a negation is the negated underlying map. -/
@[simp]
theorem neg_toRightHom {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : Hom M N) :
    toRightHom (-f) = -toRightHom f := sorry

/-- The underlying degree-zero map of a base-ring multiple is the corresponding multiple. -/
@[simp]
theorem smul_toRightHom {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (r : R) (f : Hom M N) :
    toRightHom (r • f) = r • toRightHom f := sorry

end Hom

/-- A graded bimodule morphism acts on the common underlying carrier. -/
instance instCoeFunHom (M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    CoeFun (Hom M N) (fun _ ↦ M → N) where
  coe f := Hom.toLinearMap f

/-- Evaluation of a graded bimodule morphism is evaluation of its underlying right-linear map. -/
@[simp]
theorem hom_coe_apply {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : Hom M N) (x : M) : f x = Hom.toLinearMap f x := sorry

/-- Graded bimodule morphisms are determined by their underlying degree-zero right-module maps. -/
@[ext]
theorem hom_ext {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} {f g : Hom M N}
    (h : Hom.toRightHom f = Hom.toRightHom g) : f = g := sorry

/-- Graded bimodule morphisms are determined pointwise. -/
theorem hom_ext_apply {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} {f g : Hom M N}
    (h : ∀ x : M, f x = g x) : f = g := sorry

/-- The identity graded bimodule morphism acts as the identity. -/
@[simp]
theorem id_apply (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (x : M) : Hom.id M x = x := sorry

/-- Composition of graded bimodule morphisms evaluates by ordinary function composition. -/
@[simp]
theorem comp_apply {L M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (g : Hom M N) (f : Hom L M) (x : L) : Hom.comp g f x = g (f x) := sorry

/-- Graded bimodules over fixed graded algebras form a category. -/
instance instCategory : Category (Bimodule.{x, y, w, v, u} 𝒜 𝒝) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The category of graded bimodules is preadditive. -/
instance instPreadditive : Preadditive (Bimodule.{x, y, w, v, u} 𝒜 𝒝) where
  homGroup M N := inferInstanceAs (AddCommGroup (Hom M N))
  add_comp := sorry
  comp_add := sorry

/-- The category of graded bimodules is `R`-linear. -/
instance instLinear : Linear R (Bimodule.{x, y, w, v, u} 𝒜 𝒝) where
  homModule M N := inferInstanceAs (Module R (Hom M N))
  smul_comp := sorry
  comp_smul := sorry

/-- Forget the left action of a graded bimodule, retaining its degree-zero right-module
morphisms. -/
@[stacks 0FQH "forgetful functor from graded bimodules"]
def forgetToRight :
    Bimodule.{x, y, w, v, u} 𝒜 𝒝 ⥤ Right.DegreeZero (R := R) (A := B) (𝒜 := 𝒝) where
  obj M := ⟨(M : Bimodule.{x, y, w, v, u} 𝒜 𝒝).toRight⟩
  map {M N} f := Right.degreeZeroHomEquiv M.toRight N.toRight (Hom.toRightHom f)
  map_id := sorry
  map_comp := sorry

/-- Forgetting the left action returns the stored right graded module. -/
@[simp]
theorem forgetToRight_obj_obj (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    ((forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)).obj M).obj = M.toRight := sorry

/-- On morphisms, forgetting the left action is the canonical degree-zero inclusion. -/
@[simp]
theorem forgetToRight_map_hom {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : M ⟶ N) :
    ((forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)).map f).hom =
      Right.Hom.of M.toRight N.toRight 0 (Hom.toRightHom f) := sorry

/-- Forgetting the left action is faithful. -/
instance forgetToRight_faithful :
    Functor.Faithful (forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)) where
  map_injective := sorry

/-- Forgetting the left action is additive. -/
instance forgetToRight_additive :
    (forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)).Additive := sorry

/-- Forgetting the left action is `R`-linear. -/
instance forgetToRight_linear :
    Functor.Linear R (forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)) := sorry

end GradedModule.Bimodule
