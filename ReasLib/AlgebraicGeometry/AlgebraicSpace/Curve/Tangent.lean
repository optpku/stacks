/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Types.Products
public import ReasLib.Algebra.Category.ModuleCat.LinearLift
public import ReasLib.AlgebraicGeometry.GroupoidsOver.TrivialDeformation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category

/-!
# Tangent and infinitesimal functors of curves

Square-zero lifts define the tangent functor by isomorphism classes.
Automorphisms of the trivial deformation fixing the residue arrow define the
infinitesimal functor. Both have canonical module-valued linear lifts.
-/

@[expose] public section

open CategoryTheory hiding Linear
open AlgebraicGeometry Functor Limits ZeroObject
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.GroupoidsOver
  (trivSqZero trivSqZeroHom trivSqZeroInl trivSqZeroMap specTrivSqZero
    trivSqZeroHom_comp specOverInl specOverMap specOverMap_comp_inl specOverHom)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

variable {S : Scheme.{u}} {k : Type u} [Field k]
variable (kToS : Spec (CommRingCat.of k) ⟶ S)
variable (x : (p S).Fiber (Over.mk kToS))

/-- The category of lifts of a fibre object over `Spec(k)` along a ring map
`A' ⟶ k` compatible with the structure maps to the base scheme. -/
abbrev liftCat {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S} (fA : A' ⟶ CommRingCat.of k)
    (hfA : Spec.map fA ≫ σA' = kToS) :=
  UnderLift (p S) (specOverHom fA hfA) x

/-- The type of isomorphism classes of lifts of `x` along `A' ⟶ k`. -/
def lifts {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S} (fA : A' ⟶ CommRingCat.of k)
    (hfA : Spec.map fA ≫ σA' = kToS) : Type (u + 1) :=
  isomorphismClasses.obj (Cat.of (liftCat kToS x fA hfA))

/-- The isomorphism class of a lift. -/
def lifts.mk {kToS : Spec (CommRingCat.of k) ⟶ S}
    {x : (p S).Fiber (Over.mk kToS)}
    {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ CommRingCat.of k} {hfA : Spec.map fA ≫ σA' = kToS}
    (a : liftCat kToS x fA hfA) : lifts kToS x fA hfA :=
  Quotient.mk'' a

/-- Two lifts determine the same class if and only if they are isomorphic. -/
theorem lifts.mk_eq_mk {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    {fA : A' ⟶ CommRingCat.of k} {hfA : Spec.map fA ≫ σA' = kToS}
    (a b : liftCat kToS x fA hfA) :
    lifts.mk a = lifts.mk b ↔ Nonempty (a ≅ b) :=
  sorry

/-- The trivial deformation of `x` to `Spec(k[M])`, as the selected reindexing along
the section `Spec(k[M]) ⟶ Spec(k)`. -/
def trivialDeformation (M : ModuleCat.{u} k) :
    (p S).Fiber (Over.mk (specTrivSqZero kToS M)) :=
  Chosen.reindexObj (p S) (specOverInl kToS M) x

/-- The trivial deformation of `x` to `Spec(k[M])`, as an object of the lift
category along `k[M] ⟶ k`. -/
def trivialDeformationLift (M : ModuleCat.{u} k) :
    liftCat kToS x (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M) := by
  have h : (p S).IsHomLift
      (specOverHom (trivSqZeroHom (CommRingCat.of k) M)
          (trivSqZeroHom_comp kToS M) ≫ specOverInl kToS M)
      (𝟙 (Fiber.fiberInclusion.obj x)) := by
    sorry
  exact UnderLift.ofHom
    (specOverHom (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M)) x
    (@Chosen.cartesianFactor _ _ _ _ (p S) _
      (Over.mk kToS) (Over.mk (specTrivSqZero kToS M)) (Over.mk kToS)
      (specOverInl kToS M)
      (specOverHom (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M))
      x (Fiber.fiberInclusion.obj x) (𝟙 (Fiber.fiberInclusion.obj x)) h)
    (h := @Chosen.cartesianFactor.isHomLift _ _ _ _ (p S) _ _ _ _
      (specOverInl kToS M)
      (specOverHom (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M))
      x (Fiber.fiberInclusion.obj x) (𝟙 (Fiber.fiberInclusion.obj x)) h)

/-- The trivial deformation lift is a hom-lift of the coefficient projection. -/
theorem trivialDeformationLift_isHomLift (M : ModuleCat.{u} k) :
    (p S).IsHomLift
      (specOverHom (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M))
      (trivialDeformationLift kToS x M).hom :=
  (trivialDeformationLift kToS x M).property

/-- Reindex a lift of `x` to `k[M]` along an induced map `k[M] ⟶ k[N]`. -/
def reindexLift {M N : ModuleCat.{u} k} (f : M ⟶ N)
    (a : liftCat kToS x (trivSqZeroHom (CommRingCat.of k) M)
      (trivSqZeroHom_comp kToS M)) :
    liftCat kToS x (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N) := by
  have h : (p S).IsHomLift
      (specOverHom (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N) ≫
        specOverMap kToS f) a.hom := by
    sorry
  exact UnderLift.ofHom
    (specOverHom (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N)) x
    (@Chosen.cartesianFactor _ _ _ _ (p S) _ _ _ _
      (specOverMap kToS f)
      (specOverHom (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N))
      a.codomain (Fiber.fiberInclusion.obj x) a.hom h)
    (h := @Chosen.cartesianFactor.isHomLift _ _ _ _ (p S) _ _ _ _
      (specOverMap kToS f)
      (specOverHom (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N))
      a.codomain (Fiber.fiberInclusion.obj x) a.hom h)

/-- The comparison iso identifying successive reindexing of `x` along `inl_M` and
`specOverMap f` with the trivial deformation to `k[N]`. -/
def trivialDeformationCompIso {M N : ModuleCat.{u} k} (f : M ⟶ N) :
    trivialDeformation kToS x N ≅
      Chosen.reindexObj (p S) (specOverMap kToS f)
        (trivialDeformation kToS x M) :=
  Chosen.Reindex.specifiedCompIsoApp (p S)
    (specOverInl kToS M) (specOverMap kToS f) (specOverInl kToS N)
    (specOverMap_comp_inl kToS f) x

/-- Transport an automorphism of the trivial deformation along a coefficient map. -/
def infTypeMap {M N : ModuleCat.{u} k} (f : M ⟶ N)
    (α : Aut (trivialDeformation kToS x M)) : Aut (trivialDeformation kToS x N) :=
  (trivialDeformationCompIso kToS x f) ≪≫
    (Chosen.reindex (p S) (specOverMap kToS f)).mapIso α ≪≫
    (trivialDeformationCompIso kToS x f).symm

/-- Infinitesimal automorphisms of the trivial deformation of `x` to `Spec(k[M])`. -/
def infType (M : ModuleCat.{u} k) : Type (u + 1) :=
  { α : Aut (trivialDeformation kToS x M) //
    (trivialDeformationLift kToS x M).hom ≫ Fiber.fiberInclusion.map α.hom =
      (trivialDeformationLift kToS x M).hom }

/-- Push an element of `infType` along `M ⟶ N`. -/
def infTypeFunctor_map {M N : ModuleCat.{u} k} (f : M ⟶ N) (α : infType kToS x M) :
    infType kToS x N :=
  ⟨infTypeMap kToS x f α.val, sorry⟩

/-- The Type-valued functor `M ↦ Inf(x'_M/x)` of infinitesimal automorphisms of the
trivial deformation of `x` to `Spec(k[M])`. -/
def infTypeFunctor : ModuleCat.{u} k ⥤ Type (u + 1) := by
  have laws :
      (∀ M : ModuleCat.{u} k,
        TypeCat.ofHom (infTypeFunctor_map kToS x (𝟙 M)) = 𝟙 (infType kToS x M)) ∧
      (∀ {M N P : ModuleCat.{u} k} (f : M ⟶ N) (g : N ⟶ P),
        TypeCat.ofHom (infTypeFunctor_map kToS x (f ≫ g)) =
          TypeCat.ofHom (infTypeFunctor_map kToS x f) ≫
            TypeCat.ofHom (infTypeFunctor_map kToS x g)) := by
    sorry
  exact {
    obj := infType kToS x
    map := fun f ↦ TypeCat.ofHom (infTypeFunctor_map kToS x f)
    map_id := laws.1
    map_comp := laws.2 }

/-- The value of `infTypeFunctor` at `M` is `Inf` of the trivial deformation of `x`
to `k[M]`. -/
theorem infTypeFunctor_obj (M : ModuleCat.{u} k) :
    (infTypeFunctor kToS x).obj M = infType kToS x M :=
  rfl

/-- Reindexing along a coefficient map induces a map on isomorphism classes of lifts. -/
def tangentTypeMap {M N : ModuleCat.{u} k} (f : M ⟶ N) :
    lifts kToS x (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M) →
      lifts kToS x (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N) :=
  Quotient.lift (fun a ↦ lifts.mk (reindexLift kToS x f a)) (by sorry)

/-- The functor sending a module to the isomorphism classes of its square-zero lifts. -/
def tangentTypeFunctor : ModuleCat.{u} k ⥤ Type (u + 1) := by
  have laws :
      (∀ M : ModuleCat.{u} k,
        TypeCat.ofHom (tangentTypeMap kToS x (𝟙 M)) =
          𝟙 (lifts kToS x (trivSqZeroHom (CommRingCat.of k) M)
            (trivSqZeroHom_comp kToS M))) ∧
      (∀ {M N P : ModuleCat.{u} k} (f : M ⟶ N) (g : N ⟶ P),
        TypeCat.ofHom (tangentTypeMap kToS x (f ≫ g)) =
          TypeCat.ofHom (tangentTypeMap kToS x f) ≫
            TypeCat.ofHom (tangentTypeMap kToS x g)) := by
    sorry
  exact {
    obj := fun M ↦ lifts kToS x (trivSqZeroHom (CommRingCat.of k) M)
      (trivSqZeroHom_comp kToS M)
    map := fun f ↦ TypeCat.ofHom (tangentTypeMap kToS x f)
    map_id := laws.1
    map_comp := laws.2 }

/-- The value of `tangentTypeFunctor` at `M` is `Lift(x, k[M])`. -/
theorem tangentTypeFunctor_obj (M : ModuleCat.{u} k) :
    (tangentTypeFunctor kToS x).obj M =
      lifts kToS x (trivSqZeroHom (CommRingCat.of k) M)
        (trivSqZeroHom_comp kToS M) :=
  rfl

/-- Relative automorphisms of trivial square-zero deformations preserve finite products. -/
instance instPreservesFiniteProducts_infTypeFunctor :
    PreservesFiniteProducts (infTypeFunctor kToS x) :=
  sorry

/-- `Inf` of the trivial deformation to `k[0] ≅ k` is a singleton, represented by
the identity automorphism. -/
instance instUniqueZero_infTypeFunctor : Unique ((infTypeFunctor kToS x).obj 0) where
  default := ⟨1, by
    change (trivialDeformationLift kToS x 0).hom ≫
      𝟙 (Fiber.fiberInclusion.obj (trivialDeformation kToS x 0)) = _
    exact Category.comp_id _⟩
  uniq := sorry

/-- Isomorphism classes of square-zero lifts preserve finite products. -/
instance instPreservesFiniteProducts_tangentTypeFunctor :
    PreservesFiniteProducts (tangentTypeFunctor kToS x) :=
  sorry

/-- `Lift(x, k[0])` is a singleton, represented by the trivial deformation. -/
instance instUniqueZero_tangentTypeFunctor :
    Unique ((tangentTypeFunctor kToS x).obj 0) where
  default := lifts.mk (trivialDeformationLift kToS x 0)
  uniq := sorry

/-- The module-valued linear lift of relative infinitesimal automorphisms. -/
abbrev infFunctor : ModuleCat.{u} k ⥤ ModuleCat.{u + 1} k :=
  Functor.linearLift (infTypeFunctor kToS x)

/-- The infinitesimal functor has the relative automorphism subtype as underlying type. -/
theorem infFunctor_obj (M : ModuleCat.{u} k) :
    (infFunctor kToS x).obj M = ModuleCat.of k ((infTypeFunctor kToS x).obj M) :=
  rfl

/-- The module-valued linear lift of isomorphism classes of square-zero deformations. -/
abbrev tangentFunctor : ModuleCat.{u} k ⥤ ModuleCat.{u + 1} k :=
  Functor.linearLift (tangentTypeFunctor kToS x)

/-- The tangent functor has square-zero lift classes as underlying type. -/
theorem tangentFunctor_obj (M : ModuleCat.{u} k) :
    (tangentFunctor kToS x).obj M =
      ModuleCat.of k ((tangentTypeFunctor kToS x).obj M) :=
  rfl

/-- The RS* tangent space `T_x(k)` is the value of `tangentFunctor` at the
1-dimensional vector space `k`. -/
abbrev tangentAt := (tangentFunctor kToS x).obj (ModuleCat.of k k)

/-- The RS* infinitesimal automorphism space `Inf_x(k)` is the value of
`infFunctor` at the 1-dimensional vector space `k`. -/
abbrev infAt := (infFunctor kToS x).obj (ModuleCat.of k k)

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
