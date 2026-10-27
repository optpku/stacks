/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
  zero_mem' := by
    intro a x
    change (0 : N) = a • (0 : N)
    exact (smul_zero a).symm
  add_mem' := by
    intro f g hf hg a x
    change f.1 (M.leftAction a x) + g.1 (M.leftAction a x) =
      a • (f.1 x + g.1 x)
    rw [hf a x, hg a x]
    exact (smul_add a (f.1 x) (g.1 x)).symm
  smul_mem' := by
    intro r f hf a x
    change r • f.1 (M.leftAction a x) = a • (r • f.1 x)
    rw [hf a x]
    exact smul_comm r a (f.1 x)

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
    {i : ι} {x : M} (hx : x ∈ M.grading i) : toLinearMap f x ∈ N.grading i := by
  simpa only [add_zero, toLinearMap, grading] using (toRightHom f).2 i x hx

/-- A graded bimodule morphism commutes with the left action. -/
@[simp]
theorem map_leftAction {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : Hom M N) (a : A) (x : M) :
    toLinearMap f (M.leftAction a x) = N.leftAction a (toLinearMap f x) := by
  exact f.2 a x

/-- A graded bimodule morphism commutes with the right action. -/
@[simp]
theorem map_rightAction {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : Hom M N) (x : M) (b : B) :
    toLinearMap f (M.rightAction x b) = N.rightAction (toLinearMap f x) b := by
  exact (toLinearMap f).map_smul (MulOpposite.op b) x

/-- The identity morphism of a graded bimodule. -/
def id (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) : Hom M M :=
  ⟨Right.HomogeneousMap.id M.toRight, by
    intro a x
    exact (GradedModule.HomogeneousMap.id_apply (M.leftAction a x)).trans
      (congrArg (M.leftAction a) (GradedModule.HomogeneousMap.id_apply x).symm)⟩

/-- Composition of graded bimodule morphisms. -/
def comp {L M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (g : Hom M N) (f : Hom L M) :
    Hom L N :=
  ⟨⟨(toLinearMap g).comp (toLinearMap f), by
      intro i x hx
      simpa only [LinearMap.comp_apply, add_zero, grading] using map_mem g (map_mem f hx)⟩, by
    intro a x
    change toLinearMap g (toLinearMap f (L.leftAction a x)) =
      N.leftAction a (toLinearMap g (toLinearMap f x))
    rw [map_leftAction, map_leftAction]⟩

/-- The underlying degree-zero right-module morphism of the identity is the identity. -/
@[simp]
theorem id_toRightHom (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    toRightHom (id M) = Right.HomogeneousMap.id M.toRight := rfl

/-- The underlying right-linear map of a composite is the composite of the underlying maps. -/
@[simp]
theorem comp_toLinearMap {L M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (g : Hom M N) (f : Hom L M) :
    toLinearMap (comp g f) = (toLinearMap g).comp (toLinearMap f) := rfl

/-- The underlying degree-zero map of the zero morphism is zero. -/
@[simp]
theorem zero_toRightHom (M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    toRightHom (0 : Hom M N) = 0 := rfl

/-- The underlying degree-zero map of a sum is the sum of the underlying maps. -/
@[simp]
theorem add_toRightHom {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f g : Hom M N) :
    toRightHom (f + g) = toRightHom f + toRightHom g := rfl

/-- The underlying degree-zero map of a negation is the negated underlying map. -/
@[simp]
theorem neg_toRightHom {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : Hom M N) :
    toRightHom (-f) = -toRightHom f := rfl

/-- The underlying degree-zero map of a base-ring multiple is the corresponding multiple. -/
@[simp]
theorem smul_toRightHom {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (r : R) (f : Hom M N) :
    toRightHom (r • f) = r • toRightHom f := rfl

end Hom

/-- A graded bimodule morphism acts on the common underlying carrier. -/
instance instCoeFunHom (M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    CoeFun (Hom M N) (fun _ ↦ M → N) where
  coe f := Hom.toLinearMap f

/-- Evaluation of a graded bimodule morphism is evaluation of its underlying right-linear map. -/
@[simp]
theorem hom_coe_apply {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : Hom M N) (x : M) : f x = Hom.toLinearMap f x := rfl

/-- Graded bimodule morphisms are determined by their underlying degree-zero right-module maps. -/
@[ext]
theorem hom_ext {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} {f g : Hom M N}
    (h : Hom.toRightHom f = Hom.toRightHom g) : f = g := by
  exact Subtype.ext h

/-- Graded bimodule morphisms are determined pointwise. -/
theorem hom_ext_apply {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} {f g : Hom M N}
    (h : ∀ x : M, f x = g x) : f = g := by
  apply hom_ext
  apply Subtype.ext
  exact LinearMap.ext h

/-- The identity graded bimodule morphism acts as the identity. -/
@[simp]
theorem id_apply (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (x : M) : Hom.id M x = x := by
  exact GradedModule.HomogeneousMap.id_apply x

/-- Composition of graded bimodule morphisms evaluates by ordinary function composition. -/
@[simp]
theorem comp_apply {L M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (g : Hom M N) (f : Hom L M) (x : L) : Hom.comp g f x = g (f x) := rfl

/-- Graded bimodules over fixed graded algebras form a category. -/
instance instCategory : Category (Bimodule.{x, y, w, v, u} 𝒜 𝒝) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp := by
    intro M N f
    apply hom_ext_apply
    intro x
    show Hom.comp f (Hom.id M) x = f x
    rw [comp_apply, id_apply]
  comp_id := by
    intro M N f
    apply hom_ext_apply
    intro x
    show Hom.comp (Hom.id N) f x = f x
    rw [comp_apply, id_apply]
  assoc := by
    intro K L M N f g h
    apply hom_ext_apply
    intro x
    rfl

/-- The category of graded bimodules is preadditive. -/
instance instPreadditive : Preadditive (Bimodule.{x, y, w, v, u} 𝒜 𝒝) where
  homGroup M N := inferInstanceAs (AddCommGroup (Hom M N))
  add_comp := by
    intro L M N f f' g
    apply hom_ext_apply
    intro x
    change Hom.toLinearMap g (Hom.toLinearMap f x + Hom.toLinearMap f' x) =
      Hom.toLinearMap g (Hom.toLinearMap f x) + Hom.toLinearMap g (Hom.toLinearMap f' x)
    exact map_add (Hom.toLinearMap g) _ _
  comp_add := by
    intro L M N f g g'
    apply hom_ext_apply
    intro x
    rfl

/-- The category of graded bimodules is `R`-linear. -/
instance instLinear : Linear R (Bimodule.{x, y, w, v, u} 𝒜 𝒝) where
  homModule M N := inferInstanceAs (Module R (Hom M N))
  smul_comp := by
    intro L M N r f g
    apply hom_ext_apply
    intro x
    change Hom.toLinearMap g (r • Hom.toLinearMap f x) =
      r • Hom.toLinearMap g (Hom.toLinearMap f x)
    exact (Hom.toLinearMap g).map_smul_of_tower r _
  comp_smul := by
    intro L M N f r g
    apply hom_ext_apply
    intro x
    rfl

/-- Forget the left action of a graded bimodule, retaining its degree-zero right-module
morphisms. -/
@[stacks 0FQH "forgetful functor from graded bimodules"]
def forgetToRight :
    Bimodule.{x, y, w, v, u} 𝒜 𝒝 ⥤ Right.DegreeZero (R := R) (A := B) (𝒜 := 𝒝) where
  obj M := ⟨(M : Bimodule.{x, y, w, v, u} 𝒜 𝒝).toRight⟩
  map {M N} f := Right.degreeZeroHomEquiv M.toRight N.toRight (Hom.toRightHom f)
  map_id := by
    intro M
    rfl
  map_comp := by
    intro L M N f g
    apply WideSubcategory.hom_ext
    -- Supply the linearity proofs before computing the direct-sum composition, so unfolding
    -- the ambient construction does not copy its unproved proof fields into this proof.
    let component {m : ι} (q : Right.HomogeneousMap M.toRight N.toRight m) (n : ι) :
        Right.HomogeneousMap L.toRight M.toRight n →ₗ[R]
          Right.HomogeneousMap L.toRight N.toRight (n + m) :=
      { toFun p := Right.HomogeneousMap.comp q p
        map_add' := by
          intro p p'
          apply Subtype.ext
          apply LinearMap.ext
          intro x
          change (Right.HomogeneousMap.comp q (p + p')).1 x =
            (Right.HomogeneousMap.comp q p).1 x + (Right.HomogeneousMap.comp q p').1 x
          simp only [GradedModule.HomogeneousMap.comp_apply]
          exact map_add q.1 _ _
        map_smul' := by
          intro r p
          apply Subtype.ext
          apply LinearMap.ext
          intro x
          change (Right.HomogeneousMap.comp q (r • p)).1 x =
            r • (Right.HomogeneousMap.comp q p).1 x
          simp only [GradedModule.HomogeneousMap.comp_apply]
          exact q.1.map_smul_of_tower r _ }
    let postcomp {m : ι} (q : Right.HomogeneousMap M.toRight N.toRight m) :
        Right.Hom L.toRight M.toRight →ₗ[R] Right.Hom L.toRight N.toRight :=
      DirectSum.toModule R ι (Right.Hom L.toRight N.toRight) fun n ↦
        (Right.Hom.of L.toRight N.toRight (n + m)).comp (component q n)
    let postcompLinear (m : ι) :
        Right.HomogeneousMap M.toRight N.toRight m →ₗ[R]
          Right.Hom L.toRight M.toRight →ₗ[R] Right.Hom L.toRight N.toRight :=
      { toFun q := postcomp q
        map_add' := by
          intro q q'
          apply DirectSum.linearMap_ext
          intro n
          apply LinearMap.ext
          intro p
          change postcomp (q + q') (Right.Hom.of L.toRight M.toRight n p) =
            postcomp q (Right.Hom.of L.toRight M.toRight n p) +
              postcomp q' (Right.Hom.of L.toRight M.toRight n p)
          simp only [postcomp, Right.Hom.of, DirectSum.toModule_lof, LinearMap.comp_apply]
          rw [← (Right.Hom.of L.toRight N.toRight (n + m)).map_add]
          apply congrArg (Right.Hom.of L.toRight N.toRight (n + m))
          apply Subtype.ext
          apply LinearMap.ext
          intro x
          change (Right.HomogeneousMap.comp (q + q') p).1 x =
            (Right.HomogeneousMap.comp q p).1 x + (Right.HomogeneousMap.comp q' p).1 x
          simp only [GradedModule.HomogeneousMap.comp_apply]
          rfl
        map_smul' := by
          intro r q
          apply DirectSum.linearMap_ext
          intro n
          apply LinearMap.ext
          intro p
          change postcomp (r • q) (Right.Hom.of L.toRight M.toRight n p) =
            r • postcomp q (Right.Hom.of L.toRight M.toRight n p)
          simp only [postcomp, Right.Hom.of, DirectSum.toModule_lof, LinearMap.comp_apply]
          rw [← (Right.Hom.of L.toRight N.toRight (n + m)).map_smul]
          apply congrArg (Right.Hom.of L.toRight N.toRight (n + m))
          apply Subtype.ext
          apply LinearMap.ext
          intro x
          change (Right.HomogeneousMap.comp (r • q) p).1 x =
            r • (Right.HomogeneousMap.comp q p).1 x
          simp only [GradedModule.HomogeneousMap.comp_apply]
          rfl }
    change Right.Hom.of L.toRight N.toRight 0 (Hom.toRightHom (Hom.comp g f)) =
      (DirectSum.toModule R ι _ postcompLinear
        (Right.Hom.of M.toRight N.toRight 0 (Hom.toRightHom g)))
        (Right.Hom.of L.toRight M.toRight 0 (Hom.toRightHom f))
    simp only [Right.Hom.of, DirectSum.toModule_lof, postcompLinear, postcomp, component,
      LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    have of_eq {i j : ι} (hij : i = j)
        (p : Right.HomogeneousMap L.toRight N.toRight i)
        (q : Right.HomogeneousMap L.toRight N.toRight j) (hpq : p.1 = q.1) :
        Right.Hom.of L.toRight N.toRight i p = Right.Hom.of L.toRight N.toRight j q := by
      subst j
      exact congrArg (Right.Hom.of L.toRight N.toRight i) (Subtype.ext hpq)
    apply of_eq (zero_add (0 : ι)).symm
    apply LinearMap.ext
    intro x
    exact (GradedModule.HomogeneousMap.comp_apply _ _ x).symm

/-- Forgetting the left action returns the stored right graded module. -/
@[simp]
theorem forgetToRight_obj_obj (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    ((forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)).obj M).obj = M.toRight := rfl

/-- On morphisms, forgetting the left action is the canonical degree-zero inclusion. -/
@[simp]
theorem forgetToRight_map_hom {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : M ⟶ N) :
    ((forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)).map f).hom =
      Right.Hom.of M.toRight N.toRight 0 (Hom.toRightHom f) := rfl

/-- Forgetting the left action is faithful. -/
instance forgetToRight_faithful :
    Functor.Faithful (forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)) where
  map_injective := by
    intro M N f g h
    apply hom_ext
    have h' := congrArg (fun k :
        (forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)).obj M ⟶
          (forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)).obj N ↦
        DirectSum.component R ι (fun i ↦ Right.HomogeneousMap M.toRight N.toRight i) 0
          k.hom) h
    simpa only [forgetToRight_map_hom, Right.Hom.of, DirectSum.component.lof_self] using h'

/-- Forgetting the left action is additive. -/
instance forgetToRight_additive :
    (forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)).Additive where
  map_add := by
    intro M N f g
    apply WideSubcategory.hom_ext
    change Right.Hom.of M.toRight N.toRight 0 (Hom.toRightHom f + Hom.toRightHom g) =
      Right.Hom.of M.toRight N.toRight 0 (Hom.toRightHom f) +
        Right.Hom.of M.toRight N.toRight 0 (Hom.toRightHom g)
    exact map_add _ _ _

/-- Forgetting the left action is `R`-linear. -/
instance forgetToRight_linear :
    Functor.Linear R (forgetToRight (𝒜 := 𝒜) (𝒝 := 𝒝)) where
  map_smul := by
    intro M N f r
    apply WideSubcategory.hom_ext
    change Right.Hom.of M.toRight N.toRight 0 (r • Hom.toRightHom f) =
      r • Right.Hom.of M.toRight N.toRight 0 (Hom.toRightHom f)
    exact map_smul _ _ _

end GradedModule.Bimodule
