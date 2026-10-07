module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Coherence
public import stacks_project.Chap90.Lemma_90_11_7_SquareZero
public import stacks_project.Chap98.Definition_98_18_1
public import stacks_project.Chap98.Lemma_98_21_2_InfinitesimalAut

/-!
# Lifts to trivial square-zero extensions

The type `Lift(x, A')` is the type of isomorphism classes of the fibered lift
category of `x` along `A' ⟶ A`. The trivial deformation of `x` to `Spec(A[M])` is
the selected reindexing of `x` along `Spec(A[M]) ⟶ Spec(A)`, and the associated
Type-valued functors send `M` to `Inf(x'_M/x)` and to `Lift(x, A[M])`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits ZeroObject
open TrivSqZeroExt

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The trivial square-zero extension `A[M]` as a commutative ring object. -/
def trivSqZero (A : CommRingCat.{u}) (M : ModuleCat.{u} A) : CommRingCat.{u} :=
  .of (TrivSqZeroExt A M)

/-- The coefficient projection `A[M] ⟶ A`. -/
def trivSqZeroHom (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    trivSqZero A M ⟶ A :=
  CommRingCat.ofHom (fstHom (A : Type u) A M).toRingHom

/-- The canonical section `A ⟶ A[M]`. -/
def trivSqZeroInl (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    A ⟶ trivSqZero A M :=
  CommRingCat.ofHom (inlHom A M)

/-- The induced `S`-algebra map `A[M] ⟶ A[N]` of a linear map `M ⟶ N`. -/
def trivSqZeroMap (A : CommRingCat.{u}) {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    trivSqZero A M ⟶ trivSqZero A N :=
  CommRingCat.ofHom (map f.hom).toRingHom

/-- The structure morphism `Spec(A[M]) ⟶ S` obtained from the section `A ⟶ A[M]`. -/
def specTrivSqZero {A : CommRingCat.{u}} (σA : Spec A ⟶ S) (M : ModuleCat.{u} A) :
    Spec (trivSqZero A M) ⟶ S :=
  Spec.map (trivSqZeroInl A M) ≫ σA

/-- The projection `A[M] ⟶ A` is compatible with the structure morphism of `Spec(A[M])`. -/
theorem trivSqZeroHom_comp {A : CommRingCat.{u}} (σA : Spec A ⟶ S) (M : ModuleCat.{u} A) :
    Spec.map (trivSqZeroHom A M) ≫ specTrivSqZero σA M = σA := sorry

/-- The morphism in `Over S` associated with the section `A ⟶ A[M]`. -/
def specOverInl {A : CommRingCat.{u}} (σA : Spec A ⟶ S) (M : ModuleCat.{u} A) :
    Over.mk (specTrivSqZero σA M) ⟶ Over.mk σA :=
  Over.homMk (Spec.map (trivSqZeroInl A M)) rfl

/-- The morphism in `Over S` associated with an induced map `A[M] ⟶ A[N]`. -/
def specOverMap {A : CommRingCat.{u}} (σA : Spec A ⟶ S)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    Over.mk (specTrivSqZero σA N) ⟶ Over.mk (specTrivSqZero σA M) :=
  Over.homMk (Spec.map (trivSqZeroMap A f)) sorry

/-- The square-zero maps `A[M] ⟶ A[N] ⟶ A` commute with the coefficient projections. -/
theorem trivSqZeroMap_comp_fst {A : CommRingCat.{u}} {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    trivSqZeroMap A f ≫ trivSqZeroHom A N = trivSqZeroHom A M := sorry

/-- Reindexing along `specOverMap f` after `specOverInl M` recovers `specOverInl N`. -/
theorem specOverMap_comp_inl {A : CommRingCat.{u}} (σA : Spec A ⟶ S)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    specOverMap σA f ≫ specOverInl σA M = specOverInl σA N := sorry

/-- The type of isomorphism classes of lifts of `x` along `A' ⟶ A`. -/
def lifts {X : GroupoidsOver S} {A A' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (x : X.p.Fiber (Over.mk σA)) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) : Type (u + 1) :=
  isomorphismClasses.obj (Cat.of (liftCat x fA hfA))

/-- The isomorphism class of a lift. -/
def lifts.mk {X : GroupoidsOver S} {A A' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {fA : A' ⟶ A}
    {hfA : Spec.map fA ≫ σA' = σA} (a : liftCat x fA hfA) :
    lifts x fA hfA :=
  Quotient.mk'' a

/-- Two lifts determine the same class if and only if they are isomorphic. -/
theorem lifts.mk_eq_mk {X : GroupoidsOver S} {A A' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    {x : X.p.Fiber (Over.mk σA)} {fA : A' ⟶ A}
    {hfA : Spec.map fA ≫ σA' = σA} (a b : liftCat x fA hfA) :
    lifts.mk a = lifts.mk b ↔ Nonempty (a ≅ b) := sorry


variable {X : GroupoidsOver S} {A : CommRingCat.{u}} {σA : Spec A ⟶ S}

/-- The trivial deformation of `x` to `Spec(A[M])`, as the selected reindexing along
the section `Spec(A[M]) ⟶ Spec(A)`. -/
def trivialDeformation (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    X.p.Fiber (Over.mk (specTrivSqZero σA M)) :=
  Chosen.reindexObj X.p (specOverInl σA M) x

/-- Identity of `x` lifts the composite of the coefficient projection with the
canonical section. -/
theorem trivialDeformation_id_isHomLift (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    X.p.IsHomLift
      (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) ≫ specOverInl σA M)
      (𝟙 (Fiber.fiberInclusion.obj x)) := sorry

/-- The trivial deformation of `x` to `Spec(A[M])`, as an object of the lift category
along `A[M] ⟶ A`. -/
def trivialDeformationLift (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  UnderLift.ofHom (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) x
    (@Chosen.cartesianFactor _ _ _ _ X.p _
      (Over.mk σA) (Over.mk (specTrivSqZero σA M)) (Over.mk σA)
      (specOverInl σA M)
      (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) x
      (Fiber.fiberInclusion.obj x) (𝟙 (Fiber.fiberInclusion.obj x))
      (trivialDeformation_id_isHomLift x M))

/-- The trivial deformation lift is a hom-lift of the coefficient projection. -/
theorem trivialDeformationLift_isHomLift (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) :
    X.p.IsHomLift (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M))
      (trivialDeformationLift x M).hom := sorry

/-- Reindexing a lift along `A[M] ⟶ A[N]` remains a hom-lift of the composite base
arrow. -/
theorem reindexLift_isHomLift (x : X.p.Fiber (Over.mk σA))
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (a : liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) :
    X.p.IsHomLift
      (specOverHom (trivSqZeroHom A N) (trivSqZeroHom_comp σA N) ≫ specOverMap σA f)
      a.hom := sorry

/-- Reindex a lift of `x` to `A[M]` along an induced map `A[M] ⟶ A[N]`. -/
def reindexLift (x : X.p.Fiber (Over.mk σA)) {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (a : liftCat x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)) :
    liftCat x (trivSqZeroHom A N) (trivSqZeroHom_comp σA N) :=
  UnderLift.ofHom (specOverHom (trivSqZeroHom A N) (trivSqZeroHom_comp σA N)) x
    (@Chosen.cartesianFactor _ _ _ _ X.p _ _ _ _
      (specOverMap σA f)
      (specOverHom (trivSqZeroHom A N) (trivSqZeroHom_comp σA N))
      a.codomain (Fiber.fiberInclusion.obj x) a.hom
      (reindexLift_isHomLift x f a))

/-- The comparison iso identifying successive reindexing of `x` along `inl_M` and
`specOverMap f` with the trivial deformation to `A[N]`. -/
def trivialDeformationCompIso (x : X.p.Fiber (Over.mk σA))
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    trivialDeformation x N ≅
      Chosen.reindexObj X.p (specOverMap σA f) (trivialDeformation x M) :=
  Chosen.Reindex.specifiedCompIsoApp X.p (specOverInl σA M) (specOverMap σA f)
    (specOverInl σA N) (specOverMap_comp_inl σA f) x

/-- Push an infinitesimal automorphism of the trivial deformation along `M ⟶ N`. -/
def infTypeMap (x : X.p.Fiber (Over.mk σA)) {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (α : Aut (trivialDeformation x M)) : Aut (trivialDeformation x N) :=
  let e := trivialDeformationCompIso x f
  { hom := e.hom ≫ Chosen.reindexMap X.p (specOverMap σA f) α.hom ≫ e.inv
    inv := e.hom ≫ Chosen.reindexMap X.p (specOverMap σA f) α.inv ≫ e.inv
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Infinitesimal automorphisms of the trivial deformation of `x` to `Spec(A[M])`. -/
def infType (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) : Type u :=
  { α : Aut (trivialDeformation x M) //
    α.hom.1 ≫ Chosen.cartesianHom X.p (specOverInl σA M) x =
      Chosen.cartesianHom X.p (specOverInl σA M) x }

/-- The underlying automorphism of an element of `infType`. -/
theorem infType_val (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A)
    (α : infType x M) : α.val = α.1 := sorry

/-- Push an element of `infType` along `M ⟶ N`. -/
def infTypeFunctor_map (x : X.p.Fiber (Over.mk σA)) {M N : ModuleCat.{u} A}
    (f : M ⟶ N) (α : infType x M) : infType x N :=
  ⟨infTypeMap x f α.val, sorry⟩

/-- The Type-valued functor `M ↦ Inf(x'_M/x)` of infinitesimal automorphisms of the
trivial deformation of `x` to `Spec(A[M])`. -/
def infTypeFunctor (x : X.p.Fiber (Over.mk σA)) : ModuleCat.{u} A ⥤ Type u where
  obj M := infType x M
  map f := TypeCat.ofHom (infTypeFunctor_map x f)
  map_id := sorry
  map_comp := sorry

/-- The value of `infTypeFunctor` at `M` is `Inf` of the trivial deformation of `x`
to `A[M]`. -/
theorem infTypeFunctor_obj (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (infTypeFunctor x).obj M = infType x M := sorry

/-- The Type-valued functor `M ↦ Lift(x, A[M])` of isomorphism classes of
infinitesimal deformations of `x` to `Spec(A[M])`. -/
def tangentTypeFunctor (x : X.p.Fiber (Over.mk σA)) :
    ModuleCat.{u} A ⥤ Type (u + 1) where
  obj M := lifts x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)
  map f := TypeCat.ofHom (Quotient.lift (fun a ↦ lifts.mk (reindexLift x f a)) sorry)
  map_id := sorry
  map_comp := sorry

/-- The value of `tangentTypeFunctor` at `M` is `Lift(x, A[M])`. -/
theorem tangentTypeFunctor_obj (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (tangentTypeFunctor x).obj M =
      lifts x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) := sorry

variable [HasStrongRimSchlessinger X]

/-- Under (RS*), the functor `M ↦ Inf(x'_M/x)` preserves finite products. -/
instance infTypeFunctor.preservesFiniteProducts (x : X.p.Fiber (Over.mk σA)) :
    PreservesFiniteProducts (infTypeFunctor x) := sorry

/-- Under (RS*), `Inf` of the trivial deformation to `A[0] ≅ A` is a singleton. -/
instance infTypeFunctor.uniqueZero (x : X.p.Fiber (Over.mk σA)) :
    Unique ((infTypeFunctor x).obj 0) where
  default := ⟨1, sorry⟩
  uniq := sorry

/-- Under (RS*), the functor `M ↦ Lift(x, A[M])` preserves finite products. -/
instance tangentTypeFunctor.preservesFiniteProducts (x : X.p.Fiber (Over.mk σA)) :
    PreservesFiniteProducts (tangentTypeFunctor x) := sorry

/-- Under (RS*), `Lift(x, A[0])` is a singleton, represented by the trivial
deformation. -/
instance tangentTypeFunctor.uniqueZero (x : X.p.Fiber (Over.mk σA)) :
    Unique ((tangentTypeFunctor x).obj 0) where
  default := lifts.mk (trivialDeformationLift x 0)
  uniq := sorry

end AlgebraicGeometry.GroupoidsOver
