/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Types.Products
public import stacks_project.Chap90.Definition_90_11_1_ModuleLinear
public import stacks_project.Chap90.Lemma_90_11_4_LinearLift
public import stacks_project.Chap98.Lemma_98_21_1
public import stacks_project.Chap98.Lemma_98_21_2_Lifts
public import stacks_project.Chap99.Lemma_99_13_1

/-!
# RS* infinitesimal and tangent spaces of `Spaces'_{fp, flat, proper}`

The Hom-universe of `FpFlatProperGroupoids S` is `u + 1`, so the Chap98 owners
`infFunctor` / `tangentFunctor` on `GroupoidsOver` cannot be applied. This
module rebuilds the Type-valued functors `M ↦ Inf(x'_M/x)` and
`M ↦ Lift(x, k[M])` on `pFpFlatProperGroupoids S`, using `UnderLift` and the
universe-independent square-zero algebra `trivSqZero`, then lifts them to
`k`-linear functors landing in `ModuleCat.{u + 1} k`.
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
namespace FpFlatProperGroupoids

variable {S : Scheme.{u}} {k : Type u} [Field k]
variable (kToS : Spec (CommRingCat.of k) ⟶ S)
variable (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS))

/-- The category of lifts of a fibre object `x` over `Spec(k)` along a `k`-algebra
map `A' ⟶ CommRingCat.of k`. -/
abbrev liftCat {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S} (fA : A' ⟶ CommRingCat.of k)
    (hfA : Spec.map fA ≫ σA' = kToS) :=
  UnderLift (pFpFlatProperGroupoids S) (specOverHom fA hfA) x

/-- `liftCat` is the fibered lift category of `x` along `specOverHom fA`. -/
theorem liftCat_eq {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ CommRingCat.of k) (hfA : Spec.map fA ≫ σA' = kToS) :
    liftCat kToS x fA hfA =
      UnderLift (pFpFlatProperGroupoids S) (specOverHom fA hfA) x :=
  sorry

/-- The type of isomorphism classes of lifts of `x` along `A' ⟶ k`. -/
def lifts {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S} (fA : A' ⟶ CommRingCat.of k)
    (hfA : Spec.map fA ≫ σA' = kToS) : Type (u + 1) :=
  isomorphismClasses.obj (Cat.of (liftCat kToS x fA hfA))

/-- The isomorphism class of a lift. -/
def lifts.mk {kToS : Spec (CommRingCat.of k) ⟶ S}
    {x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS)}
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
    (pFpFlatProperGroupoids S).Fiber (Over.mk (specTrivSqZero kToS M)) :=
  Chosen.reindexObj (pFpFlatProperGroupoids S) (specOverInl kToS M) x

/-- Identity of `x` lifts the composite of the coefficient projection with the
canonical section. -/
theorem trivialDeformation_id_isHomLift (M : ModuleCat.{u} k) :
    (pFpFlatProperGroupoids S).IsHomLift
      (specOverHom (trivSqZeroHom (CommRingCat.of k) M)
          (trivSqZeroHom_comp kToS M) ≫
        specOverInl kToS M)
      (𝟙 (Fiber.fiberInclusion.obj x)) :=
  sorry

/-- The trivial deformation of `x` to `Spec(k[M])`, as an object of the lift
category along `k[M] ⟶ k`. -/
def trivialDeformationLift (M : ModuleCat.{u} k) :
    liftCat kToS x (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M) :=
  UnderLift.ofHom
    (specOverHom (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M)) x
    (@Chosen.cartesianFactor _ _ _ _ (pFpFlatProperGroupoids S) _
      (Over.mk kToS) (Over.mk (specTrivSqZero kToS M)) (Over.mk kToS)
      (specOverInl kToS M)
      (specOverHom (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M))
      x (Fiber.fiberInclusion.obj x) (𝟙 (Fiber.fiberInclusion.obj x))
      (trivialDeformation_id_isHomLift kToS x M))

/-- The trivial deformation lift is a hom-lift of the coefficient projection. -/
theorem trivialDeformationLift_isHomLift (M : ModuleCat.{u} k) :
    (pFpFlatProperGroupoids S).IsHomLift
      (specOverHom (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M))
      (trivialDeformationLift kToS x M).hom :=
  sorry

/-- Reindexing a lift along `k[M] ⟶ k[N]` remains a hom-lift of the composite base
arrow. -/
theorem reindexLift_isHomLift {M N : ModuleCat.{u} k} (f : M ⟶ N)
    (a : liftCat kToS x (trivSqZeroHom (CommRingCat.of k) M)
      (trivSqZeroHom_comp kToS M)) :
    (pFpFlatProperGroupoids S).IsHomLift
      (specOverHom (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N) ≫
        specOverMap kToS f)
      a.hom :=
  sorry

/-- Reindex a lift of `x` to `k[M]` along an induced map `k[M] ⟶ k[N]`. -/
def reindexLift {M N : ModuleCat.{u} k} (f : M ⟶ N)
    (a : liftCat kToS x (trivSqZeroHom (CommRingCat.of k) M)
      (trivSqZeroHom_comp kToS M)) :
    liftCat kToS x (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N) :=
  UnderLift.ofHom
    (specOverHom (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N)) x
    (@Chosen.cartesianFactor _ _ _ _ (pFpFlatProperGroupoids S) _ _ _ _
      (specOverMap kToS f)
      (specOverHom (trivSqZeroHom (CommRingCat.of k) N) (trivSqZeroHom_comp kToS N))
      a.codomain (Fiber.fiberInclusion.obj x) a.hom
      (reindexLift_isHomLift kToS x f a))

/-- The comparison iso identifying successive reindexing of `x` along `inl_M` and
`specOverMap f` with the trivial deformation to `k[N]`. -/
def trivialDeformationCompIso {M N : ModuleCat.{u} k} (f : M ⟶ N) :
    trivialDeformation kToS x N ≅
      Chosen.reindexObj (pFpFlatProperGroupoids S) (specOverMap kToS f)
        (trivialDeformation kToS x M) :=
  Chosen.Reindex.specifiedCompIsoApp (pFpFlatProperGroupoids S)
    (specOverInl kToS M) (specOverMap kToS f) (specOverInl kToS N)
    (specOverMap_comp_inl kToS f) x

/-- Push an infinitesimal automorphism of the trivial deformation along `M ⟶ N`. -/
def infTypeMap {M N : ModuleCat.{u} k} (f : M ⟶ N)
    (α : Aut (trivialDeformation kToS x M)) : Aut (trivialDeformation kToS x N) :=
  let e := trivialDeformationCompIso kToS x f
  { hom := e.hom ≫ Chosen.reindexMap (pFpFlatProperGroupoids S) (specOverMap kToS f) α.hom ≫ e.inv
    inv := e.hom ≫ Chosen.reindexMap (pFpFlatProperGroupoids S) (specOverMap kToS f) α.inv ≫ e.inv
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Infinitesimal automorphisms of the trivial deformation of `x` to `Spec(k[M])`. -/
def infType (M : ModuleCat.{u} k) : Type (u + 1) :=
  { α : Aut (trivialDeformation kToS x M) //
    α.hom.1 ≫
        Chosen.cartesianHom (pFpFlatProperGroupoids S) (specOverInl kToS M) x =
      Chosen.cartesianHom (pFpFlatProperGroupoids S) (specOverInl kToS M) x }

/-- The underlying automorphism of an element of `infType`. -/
theorem infType_val (M : ModuleCat.{u} k) (α : infType kToS x M) : α.val = α.1 :=
  sorry

/-- Push an element of `infType` along `M ⟶ N`. -/
def infTypeFunctor_map {M N : ModuleCat.{u} k} (f : M ⟶ N) (α : infType kToS x M) :
    infType kToS x N :=
  ⟨infTypeMap kToS x f α.val, sorry⟩

/-- The Type-valued functor `M ↦ Inf(x'_M/x)` of infinitesimal automorphisms of the
trivial deformation of `x` to `Spec(k[M])`. -/
def infTypeFunctor : ModuleCat.{u} k ⥤ Type (u + 1) where
  obj M := infType kToS x M
  map f := TypeCat.ofHom (infTypeFunctor_map kToS x f)
  map_id := sorry
  map_comp := sorry

/-- The value of `infTypeFunctor` at `M` is `Inf` of the trivial deformation of `x`
to `k[M]`. -/
theorem infTypeFunctor_obj (M : ModuleCat.{u} k) :
    (infTypeFunctor kToS x).obj M = infType kToS x M :=
  sorry

/-- The Type-valued functor `M ↦ Lift(x, k[M])` of isomorphism classes of
infinitesimal deformations of `x` to `Spec(k[M])`. -/
def tangentTypeFunctor : ModuleCat.{u} k ⥤ Type (u + 1) where
  obj M :=
    lifts kToS x (trivSqZeroHom (CommRingCat.of k) M) (trivSqZeroHom_comp kToS M)
  map f := TypeCat.ofHom (Quotient.lift (fun a ↦ lifts.mk (reindexLift kToS x f a)) sorry)
  map_id := sorry
  map_comp := sorry

/-- The value of `tangentTypeFunctor` at `M` is `Lift(x, k[M])`. -/
theorem tangentTypeFunctor_obj (M : ModuleCat.{u} k) :
    (tangentTypeFunctor kToS x).obj M =
      lifts kToS x (trivSqZeroHom (CommRingCat.of k) M)
        (trivSqZeroHom_comp kToS M) :=
  sorry

/-- The stack `pFpFlatProperGroupoids` satisfies (RS*) by Lemma 99.13.7, so
`M ↦ Inf(x'_M/x)` preserves finite products. -/
instance instPreservesFiniteProducts_infTypeFunctor :
    PreservesFiniteProducts (infTypeFunctor kToS x) :=
  sorry

/-- `Inf` of the trivial deformation to `k[0] ≅ k` is a singleton, represented by
the identity automorphism. -/
instance instUniqueZero_infTypeFunctor : Unique ((infTypeFunctor kToS x).obj 0) where
  default := ⟨1, sorry⟩
  uniq := sorry

/-- The stack `pFpFlatProperGroupoids` satisfies (RS*) by Lemma 99.13.7, so
`M ↦ Lift(x, k[M])` preserves finite products. -/
instance instPreservesFiniteProducts_tangentTypeFunctor :
    PreservesFiniteProducts (tangentTypeFunctor kToS x) :=
  sorry

/-- `Lift(x, k[0])` is a singleton, represented by the trivial deformation. -/
instance instUniqueZero_tangentTypeFunctor :
    Unique ((tangentTypeFunctor kToS x).obj 0) where
  default := lifts.mk (trivialDeformationLift kToS x 0)
  uniq := sorry

/-- Addition on `Inf(x'_M/x)` induced by the sum map and the product comparison. -/
instance instAdd_infTypeFunctor (M : ModuleCat.{u} k) :
    Add ((infTypeFunctor kToS x).obj M) where
  add a b :=
    (infTypeFunctor kToS x).map (sumHom M)
      ((asIso (prodComparison (infTypeFunctor kToS x) M M)).inv
        ((Types.binaryProductIso ((infTypeFunctor kToS x).obj M)
          ((infTypeFunctor kToS x).obj M)).inv (a, b)))

/-- Zero on `Inf(x'_M/x)` induced by the unique point of `Inf(x'_0/x)`. -/
instance instZero_infTypeFunctor (M : ModuleCat.{u} k) :
    Zero ((infTypeFunctor kToS x).obj M) where
  zero :=
    (infTypeFunctor kToS x).map (0 : (0 : ModuleCat.{u} k) ⟶ M)
      (default : (infTypeFunctor kToS x).obj 0)

/-- Negation on `Inf(x'_M/x)` induced by `-𝟙 M`. -/
instance instNeg_infTypeFunctor (M : ModuleCat.{u} k) :
    Neg ((infTypeFunctor kToS x).obj M) where
  neg a := (infTypeFunctor kToS x).map (-𝟙 M) a

/-- Scalar multiplication on `Inf(x'_M/x)` induced by `r • 𝟙 M`. -/
instance instSMul_infTypeFunctor (M : ModuleCat.{u} k) :
    SMul k ((infTypeFunctor kToS x).obj M) where
  smul r a := (infTypeFunctor kToS x).map (r • 𝟙 M) a

/-- The additive group structure on `Inf(x'_M/x)`. -/
instance instAddCommGroup_infTypeFunctor (M : ModuleCat.{u} k) :
    AddCommGroup ((infTypeFunctor kToS x).obj M) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `k`-module structure on `Inf(x'_M/x)`. -/
instance instModule_infTypeFunctor (M : ModuleCat.{u} k) :
    Module k ((infTypeFunctor kToS x).obj M) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Addition on `Lift(x, k[M])` induced by the sum map and the product comparison. -/
instance instAdd_tangentTypeFunctor (M : ModuleCat.{u} k) :
    Add ((tangentTypeFunctor kToS x).obj M) where
  add a b :=
    (tangentTypeFunctor kToS x).map (sumHom M)
      ((asIso (prodComparison (tangentTypeFunctor kToS x) M M)).inv
        ((Types.binaryProductIso ((tangentTypeFunctor kToS x).obj M)
          ((tangentTypeFunctor kToS x).obj M)).inv (a, b)))

/-- Zero on `Lift(x, k[M])` induced by the unique point of `Lift(x, k[0])`. -/
instance instZero_tangentTypeFunctor (M : ModuleCat.{u} k) :
    Zero ((tangentTypeFunctor kToS x).obj M) where
  zero :=
    (tangentTypeFunctor kToS x).map (0 : (0 : ModuleCat.{u} k) ⟶ M)
      (default : (tangentTypeFunctor kToS x).obj 0)

/-- Negation on `Lift(x, k[M])` induced by `-𝟙 M`. -/
instance instNeg_tangentTypeFunctor (M : ModuleCat.{u} k) :
    Neg ((tangentTypeFunctor kToS x).obj M) where
  neg a := (tangentTypeFunctor kToS x).map (-𝟙 M) a

/-- Scalar multiplication on `Lift(x, k[M])` induced by `r • 𝟙 M`. -/
instance instSMul_tangentTypeFunctor (M : ModuleCat.{u} k) :
    SMul k ((tangentTypeFunctor kToS x).obj M) where
  smul r a := (tangentTypeFunctor kToS x).map (r • 𝟙 M) a

/-- The additive group structure on `Lift(x, k[M])`. -/
instance instAddCommGroup_tangentTypeFunctor (M : ModuleCat.{u} k) :
    AddCommGroup ((tangentTypeFunctor kToS x).obj M) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `k`-module structure on `Lift(x, k[M])`. -/
instance instModule_tangentTypeFunctor (M : ModuleCat.{u} k) :
    Module k ((tangentTypeFunctor kToS x).obj M) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The `k`-linear functor `Inf_x : Mod_k ⥤ Mod_k` lifting `M ↦ Inf(x'_M/x)`, at
the Hom-universe of `FpFlatProperGroupoids S`. -/
def infFunctor : ModuleCat.{u} k ⥤ ModuleCat.{u + 1} k where
  obj M := ModuleCat.of k ((infTypeFunctor kToS x).obj M)
  map f := ModuleCat.ofHom
    { toFun := fun a ↦ (infTypeFunctor kToS x).map f a
      map_add' := sorry
      map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- The object of `infFunctor` at `M` is the `k`-module with underlying type
`Inf(x'_M/x)`. -/
theorem infFunctor_obj (M : ModuleCat.{u} k) :
    (infFunctor kToS x).obj M = ModuleCat.of k ((infTypeFunctor kToS x).obj M) :=
  sorry

/-- `Inf_x` is module-linear over `k`. -/
instance instModuleLinear_infFunctor : ModuleLinear k (infFunctor kToS x) :=
  sorry

/-- The `k`-linear functor `T_x : Mod_k ⥤ Mod_k` lifting `M ↦ Lift(x, k[M])`, at
the Hom-universe of `FpFlatProperGroupoids S`. -/
def tangentFunctor : ModuleCat.{u} k ⥤ ModuleCat.{u + 1} k where
  obj M := ModuleCat.of k ((tangentTypeFunctor kToS x).obj M)
  map f := ModuleCat.ofHom
    { toFun := fun a ↦ (tangentTypeFunctor kToS x).map f a
      map_add' := sorry
      map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- The object of `tangentFunctor` at `M` is the `k`-module with underlying type
`Lift(x, k[M])`. -/
theorem tangentFunctor_obj (M : ModuleCat.{u} k) :
    (tangentFunctor kToS x).obj M =
      ModuleCat.of k ((tangentTypeFunctor kToS x).obj M) :=
  sorry

/-- `T_x` is module-linear over `k`. -/
instance instModuleLinear_tangentFunctor :
    ModuleLinear k (tangentFunctor kToS x) :=
  sorry

/-- The RS* tangent space `T_x(k)` is the value of `tangentFunctor` at the
1-dimensional vector space `k`. -/
abbrev tangentAt := (tangentFunctor kToS x).obj (ModuleCat.of k k)

/-- `tangentAt` is `T_x` evaluated at `k`. -/
theorem tangentAt_def :
    tangentAt kToS x = (tangentFunctor kToS x).obj (ModuleCat.of k k) :=
  sorry

/-- The RS* infinitesimal automorphism space `Inf_x(k)` is the value of
`infFunctor` at the 1-dimensional vector space `k`. -/
abbrev infAt := (infFunctor kToS x).obj (ModuleCat.of k k)

/-- `infAt` is `Inf_x` evaluated at `k`. -/
theorem infAt_def :
    infAt kToS x = (infFunctor kToS x).obj (ModuleCat.of k k) :=
  sorry

end FpFlatProperGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
