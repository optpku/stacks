module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Products
public import ReasLib.Algebra.Category.ModuleCat.LinearLift
public import ReasLib.AlgebraicGeometry.Deformation.SquareZero
public import ReasLib.AlgebraicGeometry.GroupoidsOver.TrivialDeformation

/-!
# Linear Inf and tangent functors of a deformation object

Under condition (RS*), the Type-valued functors `M ↦ Inf(x'_M/x)` and
`M ↦ Lift(x, A[M])` lift uniquely to `A`-linear functors `Inf_x` and `T_x` on
`Mod_A`. Comparison with a first-order thickening `A' ⟶ A` yields an isomorphism
`Inf_x(I) ≅ Inf(x'/x)` and an action of `T_x(I)` on `Lift(x, A')`.
-/

@[expose] public section

-- Public concrete constructions use private implementation declarations.
-- This visibility compatibility option keeps those declarations out of the public API.
set_option backward.privateInPublic true

open CategoryTheory hiding Linear
open AlgebraicGeometry Functor Limits ZeroObject
open AlgebraicGeometry.Deformation
open TrivSqZeroExt
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S} [hRS : HasStrongRimSchlessinger X]
variable {A : CommRingCat.{u}} {σA : Spec A ⟶ S}

/-- The `A`-linear functor `Inf_x : Mod_A ⥤ Mod_A` lifting `M ↦ Inf(x'_M/x)`. -/
def infFunctor (x : X.p.Fiber (Over.mk σA)) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  linearLift (infTypeFunctor x)

/-- The object of `infFunctor` at `M` is the `A`-module with underlying type
`Inf(x'_M/x)`. -/
theorem infFunctor_obj (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (infFunctor x).obj M = ModuleCat.of A ((infTypeFunctor x).obj M) := rfl

/-- `Inf_x` is module-linear over `A`. -/
instance infFunctor.instModuleLinear (x : X.p.Fiber (Over.mk σA)) :
    ModuleLinear (A : Type u) (infFunctor x) :=
  CategoryTheory.Functor.instModuleLinear (infTypeFunctor x)

/-- The tangent functor sends a module to the module of isomorphism classes of
lifts to its trivial square-zero extension. -/
def tangentFunctor (x : X.p.Fiber (Over.mk σA)) :
    ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A :=
  linearLift (tangentTypeFunctor x)

/-- The object of `tangentFunctor` at `M` is the `A`-module with underlying type
`Lift(x, A[M])`. -/
theorem tangentFunctor_obj (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (tangentFunctor x).obj M = ModuleCat.of A ((tangentTypeFunctor x).obj M) := rfl

/-- `T_x` is module-linear over `A`. -/
instance tangentFunctor.instModuleLinear (x : X.p.Fiber (Over.mk σA)) :
    ModuleLinear (A : Type u) (tangentFunctor x) :=
  CategoryTheory.Functor.instModuleLinear (tangentTypeFunctor x)

/-- The forgetful identification of the underlying type of `T_x(M)` with
`Lift(x, A[M])`. -/
def tangentForget (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    ((tangentFunctor x).obj M : Type (u + 1)) ≃
      lifts x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  Equiv.refl _

/-- The forgetful map `T_x(M) → Lift(x, A[M])` is bijective. -/
theorem tangentForget_bijective (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    Function.Bijective (tangentForget x M) := (tangentForget x M).bijective

variable {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
variable {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
variable [hSq : RingHom.IsSquareZeroExtension fA.hom]

/-- The kernel of a square-zero thickening, as an `A`-module. -/
def kernelObj (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    ModuleCat.{u} A :=
  ModuleCat.of A (kernelModule fA.hom)

/-- The fibre product `A' ×_A A'` of a thickening with itself. -/
private def doubleRing (fA : A' ⟶ A) : CommRingCat.{u} :=
  pullback fA fA

/-- The mixed fibre product `A' ×_A A[I]`. -/
private def mixedRing (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    CommRingCat.{u} :=
  pullback fA (trivSqZeroHom A (kernelObj fA))

/-- The two projections of `A' ×_A A'` agree over `A`, so their difference lands in
the kernel. -/
private theorem diffHom_mem (p : (doubleRing fA : Type u)) :
    fA.hom ((pullback.snd fA fA).hom p - (pullback.fst fA fA).hom p) = 0 := sorry

/-- The difference ring map `g : A' ×_A A' ⟶ A[I]` given by
`g(a₁, a₂) = ā₁ ⊕ (a₂ - a₁)`. -/
private def diffHom (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    doubleRing fA ⟶ trivSqZero A (kernelObj fA) :=
  CommRingCat.ofHom
    { toFun p :=
        inl (fA.hom ((pullback.fst fA fA).hom p)) +
          inr ⟨(pullback.snd fA fA).hom p - (pullback.fst fA fA).hom p, diffHom_mem p⟩
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- The first projection and `diffHom` agree over `A`. -/
private theorem diffHom_comp (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    pullback.fst fA fA ≫ fA = diffHom fA ≫ trivSqZeroHom A (kernelObj fA) := sorry

/-- The second coordinate recovered from a mixed pair is the sum of its
first coordinate and its kernel component. -/
private def mixedToDoubleSnd (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] : mixedRing fA ⟶ A' :=
  CommRingCat.ofHom
    { toFun p :=
        (pullback.fst fA (trivSqZeroHom A (kernelObj fA))).hom p +
          (snd ((pullback.snd fA (trivSqZeroHom A (kernelObj fA))).hom p)).val
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Recovering the second coordinate preserves its image in the quotient ring. -/
private theorem mixedToDouble_snd_comp (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    mixedToDoubleSnd fA ≫ fA =
      pullback.fst fA (trivSqZeroHom A (kernelObj fA)) ≫ fA := sorry

/-- The difference isomorphism `A' ×_A A' ≅ A' ×_A A[I]` sending `(a₁, a₂)` to
`(a₁, g(a₁, a₂))`. -/
private def doubleIsoMixed (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    doubleRing fA ≅ mixedRing fA where
  hom := pullback.lift (pullback.fst fA fA) (diffHom fA) (diffHom_comp fA)
  inv := pullback.lift (pullback.fst fA (trivSqZeroHom A (kernelObj fA)))
      (mixedToDoubleSnd fA) (mixedToDouble_snd_comp fA).symm
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The diagonal `A' ⟶ A' ×_A A'`. -/
private def doubleInl (fA : A' ⟶ A) : A' ⟶ doubleRing fA :=
  pullback.lift (𝟙 A') (𝟙 A') sorry

/-- The section `A' ⟶ A' ×_A A[I]` of the first projection. -/
private def mixedInl (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    A' ⟶ mixedRing fA :=
  pullback.lift (𝟙 A') (fA ≫ trivSqZeroInl A (kernelObj fA)) sorry

/-- The structure morphism `Spec(A' ×_A A') ⟶ S`. -/
private def specDouble (σA' : Spec A' ⟶ S) (fA : A' ⟶ A) :
    Spec (doubleRing fA) ⟶ S :=
  Spec.map (doubleInl fA) ≫ σA'

/-- The structure morphism `Spec(A' ×_A A[I]) ⟶ S`. -/
private def specMixed (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    Spec (mixedRing fA) ⟶ S :=
  Spec.map (mixedInl fA) ≫ σA'

/-- Compatibility of `Spec.map` of the first double projection with `specDouble`. -/
private theorem specDouble_fst_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A) :
    Spec.map (pullback.fst fA fA) ≫ specDouble σA' fA = σA' := sorry

/-- Compatibility of `Spec.map` of the second double projection with `specDouble`. -/
private theorem specDouble_snd_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A) :
    Spec.map (pullback.snd fA fA) ≫ specDouble σA' fA = σA' := sorry

/-- Compatibility of `Spec.map` of the first mixed projection with `specMixed`. -/
private theorem specMixed_fst_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    Spec.map (pullback.fst fA (trivSqZeroHom A (kernelObj fA))) ≫ specMixed σA' fA =
      σA' := sorry

/-- Compatibility of `Spec.map` of the second mixed projection with `specMixed`. -/
private theorem specMixed_snd_comp (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA)
    [RingHom.IsSquareZeroExtension fA.hom] :
    Spec.map (pullback.snd fA (trivSqZeroHom A (kernelObj fA))) ≫ specMixed σA' fA =
      specTrivSqZero σA (kernelObj fA) := sorry

/-- Compatibility of `doubleIsoMixed.inv` with the structure morphisms. -/
private theorem doubleIsoMixed_inv_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    Spec.map (doubleIsoMixed fA).inv ≫ specMixed σA' fA = specDouble σA' fA := sorry

/-- Compatibility of `doubleIsoMixed.hom` with the structure morphisms. -/
private theorem doubleIsoMixed_hom_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    Spec.map (doubleIsoMixed fA).hom ≫ specDouble σA' fA = specMixed σA' fA := sorry

/-- The first-order thickening `Spec(A) ⟶ Spec(A')` is a first-order thickening. -/
instance specOverHom_isFirstOrderThickening (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA)
    [RingHom.IsSquareZeroExtension fA.hom] :
    IsFirstOrderThickening (specOverHom fA hfA).left := sorry

/-- The affine pushout square of `Spec(A' ×_A A')` over `Spec(A)`. -/
private theorem double_isPushout (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    IsPushout (specOverHom fA hfA) (specOverHom fA hfA)
      (specOverHom (pullback.snd fA fA) (specDouble_snd_comp σA' fA))
      (specOverHom (pullback.fst fA fA) (specDouble_fst_comp σA' fA)) := sorry

/-- The affine pushout square of `Spec(A' ×_A A[I])` over `Spec(A)`. -/
private theorem mixed_isPushout (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    IsPushout
      (specOverHom (trivSqZeroHom A (kernelObj fA)) (trivSqZeroHom_comp σA (kernelObj fA)))
      (specOverHom fA hfA)
      (specOverHom (pullback.snd fA (trivSqZeroHom A (kernelObj fA)))
        (specMixed_snd_comp σA σA' fA hfA))
      (specOverHom (pullback.fst fA (trivSqZeroHom A (kernelObj fA)))
        (specMixed_fst_comp σA' fA)) := sorry

/-- The cartesian factor of `x'.hom` through the chosen reindexing of its codomain. -/
private theorem liftReindex_isHomLift {x : X.p.Fiber (Over.mk σA)} (x' : liftCat x fA hfA) :
    X.p.IsHomLift (𝟙 (Over.mk σA) ≫ specOverHom fA hfA) x'.hom := sorry

/-- The chosen reindexing of the codomain of a lift along `A' ⟶ A` is isomorphic to
`x`. -/
private def liftReindexIso {A'' : CommRingCat.{u}} {σA'' : Spec A'' ⟶ S}
    {g : A'' ⟶ A} {hg : Spec.map g ≫ σA'' = σA}
    {x : X.p.Fiber (Over.mk σA)} (x' : liftCat x g hg) :
    Chosen.reindexObj X.p (specOverHom g hg) x'.codomain ≅ x :=
  Fiber.isoMk
    { hom :=
        @IsCartesian.map _ _ _ _ X.p _ _ _ _ (specOverHom g hg) x'.hom
          (lift_isCartesian x')
          (Chosen.reindexObj X.p (specOverHom g hg) x'.codomain).1
          (Chosen.cartesianHom X.p (specOverHom g hg) x'.codomain)
          (Chosen.cartesianHom.isHomLift X.p (specOverHom g hg) x'.codomain)
      inv :=
        @Chosen.cartesianFactor _ _ _ _ X.p _ _ _ _
          (specOverHom g hg) (𝟙 (Over.mk σA)) x'.codomain
          (Fiber.fiberInclusion.obj x) x'.hom sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- The (RS*) pair of a fibre automorphism of a lift. -/
private def infPair {x : X.p.Fiber (Over.mk σA)} (x' : liftCat x fA hfA)
    (e : Aut x'.codomain) :
    (Chosen.reindex X.p (specOverHom fA hfA)) ⊡
      (Chosen.reindex X.p (specOverHom fA hfA)) where
  fst := x'.codomain
  snd := x'.codomain
  iso :=
    { hom := Chosen.reindexMap X.p (specOverHom fA hfA) e.hom
      inv := Chosen.reindexMap X.p (specOverHom fA hfA) e.inv
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- The morphism of (RS*) pairs encoding a fibre automorphism of a lift. -/
private def infPairHom {x : X.p.Fiber (Over.mk σA)} (x' : liftCat x fA hfA)
    (e : infinitesimalAut x') :
    infPair x' (1 : Aut x'.codomain) ⟶ infPair x' (1 : Aut x'.codomain) where
  fst := 𝟙 x'.codomain
  snd := e.val.hom
  w := sorry

/-- The (RS*) restriction comparison along the double pullback of a thickening. -/
private def doubleComparison (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    X.p.Fiber (Over.mk (specDouble σA' fA)) ⥤
      (Chosen.reindex X.p (specOverHom fA hfA)) ⊡
        (Chosen.reindex X.p (specOverHom fA hfA)) :=
  restrictionComparison X.p (double_isPushout σA' fA hfA).w

/-- The (RS*) restriction comparison along the mixed pullback `A' ×_A A[I]`. -/
private def mixedComparison (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    X.p.Fiber (Over.mk (specMixed σA' fA)) ⥤
      (Chosen.reindex X.p (specOverHom fA hfA)) ⊡
        (Chosen.reindex X.p
          (specOverHom (trivSqZeroHom A (kernelObj fA))
            (trivSqZeroHom_comp σA (kernelObj fA)))) :=
  restrictionComparison X.p (mixed_isPushout σA σA' fA hfA).w

/-- Inverse of `doubleComparison`, using the (RS*) equivalence instance. -/
private def doubleComparisonInv (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    ((Chosen.reindex X.p (specOverHom fA hfA)) ⊡
      (Chosen.reindex X.p (specOverHom fA hfA))) ⥤
        X.p.Fiber (Over.mk (specDouble σA' fA)) :=
  @Functor.inv _ _ _ _ (doubleComparison σA' fA hfA)
    (@restrictionComparison.instIsEquivalence S X hRS _ _ _ _
      (isAffine_Spec A) (isAffine_Spec A') (isAffine_Spec A') (isAffine_Spec (doubleRing fA))
      _ _ _ _ (specOverHom_isFirstOrderThickening fA hfA)
      (double_isPushout σA' fA hfA))

/-- Inverse of `mixedComparison`, using the (RS*) equivalence instance. -/
private def mixedComparisonInv (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    ((Chosen.reindex X.p (specOverHom fA hfA)) ⊡
      (Chosen.reindex X.p
        (specOverHom (trivSqZeroHom A (kernelObj fA))
          (trivSqZeroHom_comp σA (kernelObj fA))))) ⥤
        X.p.Fiber (Over.mk (specMixed σA' fA)) :=
  @Functor.inv _ _ _ _ (mixedComparison σA σA' fA hfA)
    (@restrictionComparison.instIsEquivalence S X hRS _ _ _ _
      (isAffine_Spec A) (isAffine_Spec (trivSqZero A (kernelObj fA)))
      (isAffine_Spec A') (isAffine_Spec (mixedRing fA))
      _ _ _ _ (@specOverHom_isFirstOrderThickening S A σA
        (trivSqZero A (kernelObj fA)) (specTrivSqZero σA (kernelObj fA))
        (trivSqZeroHom A (kernelObj fA)) (trivSqZeroHom_comp σA (kernelObj fA))
        AlgebraicGeometry.Deformation.instIsSquareZeroExtension_fstHom)
      (mixed_isPushout σA σA' fA hfA))

/-- Pair two lifts of `x` along `A' ⟶ A` as an object of the 2-fibre product of
restriction. -/
private def liftsPair {x : X.p.Fiber (Over.mk σA)} (a b : liftCat x fA hfA) :
    (Chosen.reindex X.p (specOverHom fA hfA)) ⊡
      (Chosen.reindex X.p (specOverHom fA hfA)) where
  fst := a.codomain
  snd := b.codomain
  iso := (liftReindexIso a).trans (liftReindexIso b).symm

/-- Pair a lift along `A' ⟶ A` with a lift along `A[I] ⟶ A`. -/
private def mixPair {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (i : liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA))) :
    (Chosen.reindex X.p (specOverHom fA hfA)) ⊡
      (Chosen.reindex X.p
        (specOverHom (trivSqZeroHom A (kernelObj fA))
          (trivSqZeroHom_comp σA (kernelObj fA)))) where
  fst := a.codomain
  snd := i.codomain
  iso := (liftReindexIso a).trans (liftReindexIso i).symm

/-- The fibre object over `Spec(A' ×_A A[I])` associated to a mixed pair of lifts
by (RS*). -/
private def mixFiber {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (i : liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA))) :
    X.p.Fiber (Over.mk (specMixed σA' fA)) :=
  (mixedComparisonInv σA σA' fA hfA).obj (mixPair a i)

/-- Transport a mixed fibre object to the double pullback along
`A' ×_A A' ≅ A' ×_A A[I]`. -/
private def transportMixed (y : X.p.Fiber (Over.mk (specMixed σA' fA))) :
    X.p.Fiber (Over.mk (specDouble σA' fA)) :=
  Chosen.reindexObj X.p
    (specOverHom (doubleIsoMixed fA).inv (doubleIsoMixed_inv_comp σA' fA)) y

/-- Restrict a double fibre object along the second projection `A' ×_A A' ⟶ A'`. -/
private def restrictDoubleSnd (y : X.p.Fiber (Over.mk (specDouble σA' fA))) :
    X.p.Fiber (Over.mk σA') :=
  Chosen.reindexObj X.p
    (specOverHom (pullback.snd fA fA) (specDouble_snd_comp σA' fA)) y

/-- Restrict a mixed fibre object along `A' ×_A A[I] ⟶ A[I]`. -/
private def restrictMixedSnd (y : X.p.Fiber (Over.mk (specMixed σA' fA))) :
    X.p.Fiber (Over.mk (specTrivSqZero σA (kernelObj fA))) :=
  Chosen.reindexObj X.p
    (specOverHom (pullback.snd fA (trivSqZeroHom A (kernelObj fA)))
      (specMixed_snd_comp σA σA' fA hfA)) y

/-- Package a fibre object over `Spec(A')` as a lift of its reindexing along
`Spec(A') ⟶ Spec(A)`. -/
private def liftOfFiber (y : X.p.Fiber (Over.mk σA')) :
    liftCat (Chosen.reindexObj X.p (specOverHom fA hfA) y) fA hfA :=
  @UnderLift.ofHom _ _ _ _ X.p _ _ _
    (Chosen.reindexObj X.p (specOverHom fA hfA) y) _
    (Chosen.cartesianHom X.p (specOverHom fA hfA) y)
    (Chosen.cartesianHom.isHomLift X.p (specOverHom fA hfA) y)

/-- The combined deformation restricts canonically to the original fibre object. -/
private def combineLiftReindexIso {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (i : liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA))) :
    Chosen.reindexObj X.p (specOverHom fA hfA)
      (restrictDoubleSnd (transportMixed (mixFiber a i))) ≅ x :=
  let r := specOverHom fA hfA
  let s := specOverHom (pullback.snd fA fA) (specDouble_snd_comp σA' fA)
  let h := specOverHom (doubleIsoMixed fA).inv (doubleIsoMixed_inv_comp σA' fA)
  let c := specOverHom (pullback.fst fA (trivSqZeroHom A (kernelObj fA)))
    (specMixed_fst_comp σA' fA)
  let y := mixFiber a i
  let E := @Functor.asEquivalence _ _ _ _ (mixedComparison σA σA' fA hfA)
    (@restrictionComparison.instIsEquivalence S X hRS _ _ _ _
      (isAffine_Spec A) (isAffine_Spec (trivSqZero A (kernelObj fA)))
      (isAffine_Spec A') (isAffine_Spec (mixedRing fA))
      _ _ _ _ (@specOverHom_isFirstOrderThickening S A σA
        (trivSqZero A (kernelObj fA)) (specTrivSqZero σA (kernelObj fA))
        (trivSqZeroHom A (kernelObj fA)) (trivSqZeroHom_comp σA (kernelObj fA))
        AlgebraicGeometry.Deformation.instIsSquareZeroExtension_fstHom)
      (mixed_isPushout σA σA' fA hfA))
  let e := (CategoricalPullback.π₁ _ _).mapIso (E.counitIso.app (mixPair a i))
  (Chosen.Reindex.compIsoApp X.p s r (transportMixed y)).symm ≪≫
    (Chosen.Reindex.specifiedCompIsoApp X.p h (r ≫ s) (r ≫ c) (by sorry) y).symm ≪≫
    Chosen.Reindex.compIsoApp X.p c r y ≪≫
    (Chosen.reindex X.p r).mapIso e ≪≫ liftReindexIso a

/-- Combining a lift with a tangent deformation uses the mixed pullback
equivalence and the second projection of the double pullback. -/
private def combineLift {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (i : liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA))) :
    liftCat x fA hfA :=
  let y := restrictDoubleSnd (transportMixed (mixFiber a i))
  @UnderLift.ofHom _ _ _ _ X.p _ _ _ x _
    (Fiber.fiberInclusion.map (combineLiftReindexIso a i).inv ≫
      Chosen.cartesianHom X.p (specOverHom fA hfA) y)
    (by
      exact @IsHomLift.comp_lift_id_left _ _ _ _ X.p _ _ _ _ _
        (specOverHom fA hfA) (Chosen.cartesianHom X.p (specOverHom fA hfA) y)
        (Chosen.cartesianHom.isHomLift X.p (specOverHom fA hfA) y)
        (Fiber.fiberInclusion.map (combineLiftReindexIso a i).inv)
        (combineLiftReindexIso a i).inv.property)

/-- The (RS*) mixed pair morphism with identity on `x'` and an infinitesimal
automorphism of the trivial deformation on the second factor. -/
private def mixPairHom {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (α : infType x (kernelObj fA)) :
    mixPair a (trivialDeformationLift x (kernelObj fA)) ⟶
      mixPair a (trivialDeformationLift x (kernelObj fA)) where
  fst := 𝟙 a.codomain
  snd := α.val.hom
  w := sorry

/-- The zero-tangent mixed gluing has second double restriction canonically
isomorphic to the given lift. -/
private def mixPairZeroSndIso {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA) :
    ((doubleComparison σA' fA hfA).obj
      (transportMixed (mixFiber a (trivialDeformationLift x (kernelObj fA))))).snd ≅
        a.codomain :=
  let d := specOverHom (doubleInl fA) (rfl : Spec.map (doubleInl fA) ≫ σA' = specDouble σA' fA)
  let h := specOverHom (doubleIsoMixed fA).hom (doubleIsoMixed_hom_comp σA' fA hfA)
  let k := specOverHom (doubleIsoMixed fA).inv (doubleIsoMixed_inv_comp σA' fA)
  let m₁ := specOverHom (pullback.fst fA (trivSqZeroHom A (kernelObj fA)))
    (specMixed_fst_comp σA' fA)
  let m₂ := specOverHom (pullback.snd fA (trivSqZeroHom A (kernelObj fA)))
    (specMixed_snd_comp σA σA' fA hfA)
  let s := specOverHom (pullback.snd fA fA) (specDouble_snd_comp σA' fA)
  let r := specOverHom fA hfA
  let j := specOverInl σA (kernelObj fA)
  let D := Chosen.reindexObj X.p d a.codomain
  let z := Chosen.reindexObj X.p h D
  let collapse := (Chosen.Reindex.compIsoApp X.p d h a.codomain).symm
  let e₁ : ((mixedComparison σA σA' fA hfA).obj z).fst ≅ a.codomain :=
    (Chosen.reindex X.p m₁).mapIso collapse ≪≫
      (Chosen.Reindex.specifiedCompIsoApp X.p (h ≫ d) m₁ (𝟙 (Over.mk σA'))
        (by sorry) a.codomain).symm ≪≫
      Chosen.Reindex.eqId.isoApp X.p (𝟙 (Over.mk σA')) rfl a.codomain
  let e₂ : ((mixedComparison σA σA' fA hfA).obj z).snd ≅
      trivialDeformation x (kernelObj fA) :=
    (Chosen.reindex X.p m₂).mapIso collapse ≪≫
      (Chosen.Reindex.specifiedCompIsoApp X.p (h ≫ d) m₂ (j ≫ r)
        (by sorry) a.codomain).symm ≪≫
      Chosen.Reindex.compIsoApp X.p r j a.codomain ≪≫
      (Chosen.reindex X.p j).mapIso (liftReindexIso a)
  let e : (mixedComparison σA σA' fA hfA).obj z ≅
      mixPair a (trivialDeformationLift x (kernelObj fA)) :=
    CategoricalPullback.mkIso e₁ e₂ (by sorry)
  let E := @Functor.asEquivalence _ _ _ _ (mixedComparison σA σA' fA hfA)
    (@restrictionComparison.instIsEquivalence S X hRS _ _ _ _
      (isAffine_Spec A) (isAffine_Spec (trivSqZero A (kernelObj fA)))
      (isAffine_Spec A') (isAffine_Spec (mixedRing fA))
      _ _ _ _ (@specOverHom_isFirstOrderThickening S A σA
        (trivSqZero A (kernelObj fA)) (specTrivSqZero σA (kernelObj fA))
        (trivSqZeroHom A (kernelObj fA)) (trivSqZeroHom_comp σA (kernelObj fA))
        AlgebraicGeometry.Deformation.instIsSquareZeroExtension_fstHom)
      (mixed_isPushout σA σA' fA hfA))
  let e' := E.inverse.mapIso e.symm ≪≫ (E.unitIso.app z).symm
  (Chosen.reindex X.p s).mapIso ((Chosen.reindex X.p k).mapIso e') ≪≫
    (Chosen.reindex X.p s).mapIso
      ((Chosen.Reindex.specifiedCompIsoApp X.p h k (𝟙 (Over.mk (specDouble σA' fA)))
        (by sorry) D).symm ≪≫
        Chosen.Reindex.eqId.isoApp X.p (𝟙 (Over.mk (specDouble σA' fA))) rfl D) ≪≫
    (Chosen.Reindex.specifiedCompIsoApp X.p d s (𝟙 (Over.mk σA'))
      (by sorry) a.codomain).symm ≪≫
    Chosen.Reindex.eqId.isoApp X.p (𝟙 (Over.mk σA')) rfl a.codomain

/-- The reverse (RS*) mixed pair morphism associated to an infinitesimal
automorphism of the trivial deformation. -/
private def mixPairHomInv {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (α : infType x (kernelObj fA)) :
    mixPair a (trivialDeformationLift x (kernelObj fA)) ⟶
      mixPair a (trivialDeformationLift x (kernelObj fA)) where
  fst := 𝟙 a.codomain
  snd := α.val.inv
  w := sorry

/-- The (RS*) automorphism of `x'` associated to an infinitesimal automorphism of
the trivial deformation. -/
private def infCompareAut (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
    (α : infType x (kernelObj fA)) : Aut x'.codomain :=
  let χ := (doubleComparison σA' fA hfA).map
    (Chosen.reindexMap X.p
      (specOverHom (doubleIsoMixed fA).inv (doubleIsoMixed_inv_comp σA' fA))
      ((mixedComparisonInv σA σA' fA hfA).map (mixPairHom x' α)))
  let χinv := (doubleComparison σA' fA hfA).map
    (Chosen.reindexMap X.p
      (specOverHom (doubleIsoMixed fA).inv (doubleIsoMixed_inv_comp σA' fA))
      ((mixedComparisonInv σA σA' fA hfA).map (mixPairHomInv x' α)))
  let e := mixPairZeroSndIso x'
  { hom := e.inv ≫ χ.snd ≫ e.hom
    inv := e.inv ≫ χinv.snd ≫ e.hom
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Additive structure on `Inf(x'/x)` from the automorphism group law. -/
instance infinitesimalAut.instAdd {x : X.p.Fiber (Over.mk σA)}
    (x' : liftCat x fA hfA) : Add (infinitesimalAut x') where
  add α β := α * β

/-- Zero on `Inf(x'/x)` is the identity automorphism. -/
instance infinitesimalAut.instZero {x : X.p.Fiber (Over.mk σA)}
    (x' : liftCat x fA hfA) : Zero (infinitesimalAut x') where
  zero := 1

/-- Negation on `Inf(x'/x)` is inversion in the automorphism group. -/
instance infinitesimalAut.instNeg {x : X.p.Fiber (Over.mk σA)}
    (x' : liftCat x fA hfA) : Neg (infinitesimalAut x') where
  neg α := α⁻¹

/-- The additive group structure on `Inf(x'/x)`. -/
instance infinitesimalAut.instAddCommGroup
    [HasStrongRimSchlessinger X] [RingHom.IsSquareZeroExtension fA.hom]
    {x : X.p.Fiber (Over.mk σA)}
    (x' : liftCat x fA hfA) : AddCommGroup (infinitesimalAut x') where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The identity-glued double pair has mixed second restriction canonically
isomorphic to the trivial deformation, using the diagonal. -/
private def infPairOneSndIso (x : X.p.Fiber (Over.mk σA)) (a : liftCat x fA hfA) :
    restrictMixedSnd (hfA := hfA)
      (Chosen.reindexObj X.p
        (specOverHom (doubleIsoMixed fA).hom (doubleIsoMixed_hom_comp σA' fA hfA))
        ((doubleComparisonInv σA' fA hfA).obj (infPair a (1 : Aut a.codomain)))) ≅
      trivialDeformation x (kernelObj fA) :=
  let d := specOverHom (doubleInl fA) (rfl : Spec.map (doubleInl fA) ≫ σA' = specDouble σA' fA)
  let h := specOverHom (doubleIsoMixed fA).hom (doubleIsoMixed_hom_comp σA' fA hfA)
  let p₁ := specOverHom (pullback.fst fA fA) (specDouble_fst_comp σA' fA)
  let p₂ := specOverHom (pullback.snd fA fA) (specDouble_snd_comp σA' fA)
  let m₂ := specOverHom (pullback.snd fA (trivSqZeroHom A (kernelObj fA)))
    (specMixed_snd_comp σA σA' fA hfA)
  let r := specOverHom fA hfA
  let j := specOverInl σA (kernelObj fA)
  let D := Chosen.reindexObj X.p d a.codomain
  let e₁ : ((doubleComparison σA' fA hfA).obj D).fst ≅ a.codomain :=
    (Chosen.Reindex.specifiedCompIsoApp X.p d p₁ (𝟙 (Over.mk σA'))
      (by sorry) a.codomain).symm ≪≫
      Chosen.Reindex.eqId.isoApp X.p (𝟙 (Over.mk σA')) rfl a.codomain
  let e₂ : ((doubleComparison σA' fA hfA).obj D).snd ≅ a.codomain :=
    (Chosen.Reindex.specifiedCompIsoApp X.p d p₂ (𝟙 (Over.mk σA'))
      (by sorry) a.codomain).symm ≪≫
      Chosen.Reindex.eqId.isoApp X.p (𝟙 (Over.mk σA')) rfl a.codomain
  let e : (doubleComparison σA' fA hfA).obj D ≅ infPair a (1 : Aut a.codomain) :=
    CategoricalPullback.mkIso e₁ e₂ (by sorry)
  let E := @Functor.asEquivalence _ _ _ _ (doubleComparison σA' fA hfA)
    (@restrictionComparison.instIsEquivalence S X hRS _ _ _ _
      (isAffine_Spec A) (isAffine_Spec A') (isAffine_Spec A') (isAffine_Spec (doubleRing fA))
      _ _ _ _ (specOverHom_isFirstOrderThickening fA hfA)
      (double_isPushout σA' fA hfA))
  let e' := E.inverse.mapIso e.symm ≪≫ (E.unitIso.app D).symm
  (Chosen.reindex X.p m₂).mapIso ((Chosen.reindex X.p h).mapIso e') ≪≫
    (Chosen.reindex X.p m₂).mapIso
      (Chosen.Reindex.compIsoApp X.p d h a.codomain).symm ≪≫
    (Chosen.Reindex.specifiedCompIsoApp X.p (h ≫ d) m₂ (j ≫ r)
      (by sorry) a.codomain).symm ≪≫
    Chosen.Reindex.compIsoApp X.p r j a.codomain ≪≫
    (Chosen.reindex X.p j).mapIso (liftReindexIso a)

/-- An infinitesimal automorphism of a lift induces an automorphism of the
trivial deformation through the fixed identity-glued pair. -/
private def infIsoInvAut (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
    (β : infinitesimalAut x') : Aut (trivialDeformation x (kernelObj fA)) :=
  let h := specOverHom (doubleIsoMixed fA).hom (doubleIsoMixed_hom_comp σA' fA hfA)
  let m₂ := specOverHom (pullback.snd fA (trivSqZeroHom A (kernelObj fA)))
    (specMixed_snd_comp σA σA' fA hfA)
  let ψ := Chosen.reindexMap X.p m₂
    (Chosen.reindexMap X.p h
      ((doubleComparisonInv σA' fA hfA).map (infPairHom x' β)))
  let ψinv := Chosen.reindexMap X.p m₂
    (Chosen.reindexMap X.p h
      ((doubleComparisonInv σA' fA hfA).map (infPairHom x' β⁻¹)))
  let e := infPairOneSndIso x x'
  { hom := e.inv ≫ ψ ≫ e.hom
    inv := e.inv ≫ ψinv ≫ e.hom
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The reverse (RS*) difference `Inf(x'/x) → Inf_x(I)`. -/
private def infIsoInv (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
    (β : infinitesimalAut x') : (infFunctor x).obj (kernelObj fA) :=
  ⟨infIsoInvAut x x' β, sorry⟩

/-- The forward comparison `Inf_x(I) → Inf(x'/x)` of the (RS*) difference pairing. -/
private def infIsoHom (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
    (α : (infFunctor x).obj (kernelObj fA)) : infinitesimalAut x' :=
  ⟨infCompareAut x x' α, sorry⟩

/-- Scalar multiplication on `Inf(x'/x)` transported from `Inf_x(I)` along the
(RS*) comparison. -/
instance infinitesimalAut.instSMul {x : X.p.Fiber (Over.mk σA)}
    (x' : liftCat x fA hfA) : SMul A (infinitesimalAut x') where
  smul r α := infIsoHom x x' (r • infIsoInv x x' α)

/-- The `A`-module structure on `Inf(x'/x)`. -/
instance infinitesimalAut.instModule {x : X.p.Fiber (Over.mk σA)}
    (x' : liftCat x fA hfA) : Module A (infinitesimalAut x') where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The isomorphism `Inf_x(I) ≅ Inf(x'/x)` of `A`-modules. -/
def infIso (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA) :
    (infFunctor x).obj (kernelObj fA) ≅ ModuleCat.of A (infinitesimalAut x') where
  hom := ModuleCat.ofHom
    { toFun := infIsoHom x x'
      map_add' := sorry
      map_smul' := sorry }
  inv := ModuleCat.ofHom
    { toFun := infIsoInv x x'
      map_add' := sorry
      map_smul' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying map of `infIso` is `infIsoHom`. -/
theorem infIso_apply (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
    (α : (infFunctor x).obj (kernelObj fA)) :
    (infIso x x').hom α = infIsoHom x x' α := rfl

/-- Addition in the infinitesimal functor agrees with composition of automorphisms. -/
theorem infFunctor_add_val (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A)
    (α β : (infFunctor x).obj M) :
    (α + β).val = α.val * β.val := sorry

/-- The action `T_x(I) × Lift(x, A') → Lift(x, A')` of infinitesimal deformations
on lifts along a first-order thickening. -/
def tangentAction (x : X.p.Fiber (Over.mk σA))
    (t : (tangentFunctor x).obj (kernelObj fA))
    (ξ : lifts x fA hfA) : lifts x fA hfA :=
  Quotient.lift₂
    (fun (a : liftCat x fA hfA)
      (i : liftCat x (trivSqZeroHom A (kernelObj fA))
        (trivSqZeroHom_comp σA (kernelObj fA))) ↦
      lifts.mk (combineLift a i))
    sorry ξ (tangentForget x (kernelObj fA) t)

/-- Applying the zero tangent vector does not change a lift. -/
theorem tangentAction_zero (x : X.p.Fiber (Over.mk σA)) (ξ : lifts x fA hfA) :
    tangentAction x (0 : (tangentFunctor x).obj (kernelObj fA)) ξ = ξ := sorry

/-- Acting by a sum of tangent vectors is the composite of their actions. -/
theorem tangentAction_add (x : X.p.Fiber (Over.mk σA))
    (s t : (tangentFunctor x).obj (kernelObj fA)) (ξ : lifts x fA hfA) :
    tangentAction x (s + t) ξ = tangentAction x s (tangentAction x t ξ) := sorry

/-- The action of `T_x(I)` on a nonempty set of lifts is simply transitive. -/
theorem tangentAction_simplyTransitive (x : X.p.Fiber (Over.mk σA))
    [Nonempty (lifts x fA hfA)] (ξ η : lifts x fA hfA) :
    ∃! t : (tangentFunctor x).obj (kernelObj fA), tangentAction x t ξ = η := sorry

end AlgebraicGeometry.GroupoidsOver
