module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Products
public import stacks_project.Chap90.Definition_90_11_1_ModuleLinear
public import stacks_project.Chap90.Lemma_90_11_4_LinearLift
public import stacks_project.Chap98.Remark_98_21_5_Thickening
public import stacks_project.Chap98.Lemma_98_21_2_Lifts

/-!
# Linear Inf and tangent functors of a deformation object

Under condition (RS*), the Type-valued functors `M ↦ Inf(x'_M/x)` and
`M ↦ Lift(x, A[M])` lift uniquely to `A`-linear functors `Inf_x` and `T_x` on
`Mod_A`. Comparison with a first-order thickening `A' ⟶ A` yields an isomorphism
`Inf_x(I) ≅ Inf(x'/x)` and an action of `T_x(I)` on `Lift(x, A')`.
-/

@[expose] public section

open CategoryTheory hiding Linear
open AlgebraicGeometry Functor Limits ZeroObject
open AlgebraicGeometry.Deformation
open TrivSqZeroExt
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
variable {A : CommRingCat.{u}} {σA : Spec A ⟶ S}

/-- The `A`-linear functor `Inf_x : Mod_A ⥤ Mod_A` lifting `M ↦ Inf(x'_M/x)`. -/
def infFunctor (x : X.p.Fiber (Over.mk σA)) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  linearLift (infTypeFunctor x)

/-- The object of `infFunctor` at `M` is the `A`-module with underlying type
`Inf(x'_M/x)`. -/
theorem infFunctor_obj (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (infFunctor x).obj M = ModuleCat.of A ((infTypeFunctor x).obj M) := sorry

/-- `Inf_x` is module-linear over `A`. -/
instance infFunctor.instModuleLinear (x : X.p.Fiber (Over.mk σA)) :
    ModuleLinear (A : Type u) (infFunctor x) :=
  CategoryTheory.Functor.instModuleLinear (infTypeFunctor x)

/-- Addition on `Lift(x, A[M])` induced by the sum map and the product comparison. -/
instance tangentTypeFunctor.instAdd (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    Add ((tangentTypeFunctor x).obj M) where
  add a b :=
    (tangentTypeFunctor x).map (sumHom M)
      ((asIso (prodComparison (tangentTypeFunctor x) M M)).inv
        ((Types.binaryProductIso ((tangentTypeFunctor x).obj M)
          ((tangentTypeFunctor x).obj M)).inv (a, b)))

/-- Zero on `Lift(x, A[M])` induced by the unique point of `Lift(x, A[0])`. -/
instance tangentTypeFunctor.instZero (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    Zero ((tangentTypeFunctor x).obj M) where
  zero := (tangentTypeFunctor x).map (0 : (0 : ModuleCat.{u} A) ⟶ M)
    (default : (tangentTypeFunctor x).obj 0)

/-- Negation on `Lift(x, A[M])` induced by `-𝟙 M`. -/
instance tangentTypeFunctor.instNeg (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    Neg ((tangentTypeFunctor x).obj M) where
  neg a := (tangentTypeFunctor x).map (-𝟙 M) a

/-- Scalar multiplication on `Lift(x, A[M])` induced by `r • 𝟙 M`. -/
instance tangentTypeFunctor.instSMul (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    SMul A ((tangentTypeFunctor x).obj M) where
  smul r a := (tangentTypeFunctor x).map (r • 𝟙 M) a

/-- The additive group structure on `Lift(x, A[M])`. -/
instance tangentTypeFunctor.instAddCommGroup (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) : AddCommGroup ((tangentTypeFunctor x).obj M) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- The `A`-module structure on `Lift(x, A[M])`. -/
instance tangentTypeFunctor.instModule (x : X.p.Fiber (Over.mk σA))
    (M : ModuleCat.{u} A) : Module A ((tangentTypeFunctor x).obj M) where
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The `A`-linear functor `T_x : Mod_A ⥤ Mod_A` lifting `M ↦ Lift(x, A[M])`, at the
universe of isomorphism classes of lifts. -/
def tangentFunctor (x : X.p.Fiber (Over.mk σA)) :
    ModuleCat.{u} A ⥤ ModuleCat.{u + 1} A where
  obj M := ModuleCat.of A ((tangentTypeFunctor x).obj M)
  map f := ModuleCat.ofHom
    { toFun := fun a ↦ (tangentTypeFunctor x).map f a
      map_add' := sorry
      map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- The object of `tangentFunctor` at `M` is the `A`-module with underlying type
`Lift(x, A[M])`. -/
theorem tangentFunctor_obj (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (tangentFunctor x).obj M = ModuleCat.of A ((tangentTypeFunctor x).obj M) := sorry

/-- `T_x` is module-linear over `A`. -/
instance tangentFunctor.instModuleLinear (x : X.p.Fiber (Over.mk σA)) :
    ModuleLinear (A : Type u) (tangentFunctor x) := sorry

/-- The forgetful identification of the underlying type of `T_x(M)` with
`Lift(x, A[M])`. -/
def tangentForget (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    ((tangentFunctor x).obj M : Type (u + 1)) ≃
      lifts x (trivSqZeroHom A M) (trivSqZeroHom_comp σA M) :=
  Equiv.refl _

/-- The forgetful map `T_x(M) → Lift(x, A[M])` is bijective. -/
theorem tangentForget_bijective (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    Function.Bijective (tangentForget x M) := sorry

variable {A' : CommRingCat.{u}} {σA' : Spec A' ⟶ S}
variable {fA : A' ⟶ A} {hfA : Spec.map fA ≫ σA' = σA}
variable [RingHom.IsSquareZeroExtension fA.hom]

/-- The kernel of a square-zero thickening, as an `A`-module. -/
def kernelObj (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    ModuleCat.{u} A :=
  ModuleCat.of A (kernelModule fA.hom)

/-- The coefficient projection of `A[I]` is a square-zero extension. -/
instance trivSqZeroHom_isSquareZero (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    (trivSqZeroHom A M).hom.IsSquareZeroExtension := sorry

/-- The fibre product `A' ×_A A'` of a thickening with itself. -/
def doubleRing (fA : A' ⟶ A) : CommRingCat.{u} :=
  pullback fA fA

/-- The mixed fibre product `A' ×_A A[I]`. -/
def mixedRing (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    CommRingCat.{u} :=
  pullback fA (trivSqZeroHom A (kernelObj fA))

/-- The two projections of `A' ×_A A'` agree over `A`, so their difference lands in
the kernel. -/
theorem diffHom_mem (p : (doubleRing fA : Type u)) :
    fA.hom ((pullback.snd fA fA).hom p - (pullback.fst fA fA).hom p) = 0 := sorry

/-- The source ring map `g : A' ×_A A' ⟶ A[I]` given by
`g(a₁, a₂) = ā₁ ⊕ (a₂ - a₁)`. -/
def diffHom (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
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
theorem diffHom_comp (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    pullback.fst fA fA ≫ fA = diffHom fA ≫ trivSqZeroHom A (kernelObj fA) := sorry

/-- The second mixed projection of `(a', ā ⊕ i)` recovers `a' + i` in `A'`. -/
theorem mixedToDouble_snd_comp (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    CommRingCat.ofHom
        { toFun p :=
            (pullback.fst fA (trivSqZeroHom A (kernelObj fA))).hom p +
              (snd ((pullback.snd fA (trivSqZeroHom A (kernelObj fA))).hom p)).val
          map_one' := sorry
          map_mul' := sorry
          map_zero' := sorry
          map_add' := sorry } ≫
      fA =
      pullback.fst fA (trivSqZeroHom A (kernelObj fA)) ≫ fA := sorry

/-- The source isomorphism `A' ×_A A' ≅ A' ×_A A[I]` sending `(a₁, a₂)` to
`(a₁, g(a₁, a₂))`. -/
def doubleIsoMixed (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    doubleRing fA ≅ mixedRing fA where
  hom := pullback.lift (pullback.fst fA fA) (diffHom fA) (diffHom_comp fA)
  inv := pullback.lift (pullback.fst fA (trivSqZeroHom A (kernelObj fA)))
      (CommRingCat.ofHom
        { toFun p :=
            (pullback.fst fA (trivSqZeroHom A (kernelObj fA))).hom p +
              (snd ((pullback.snd fA (trivSqZeroHom A (kernelObj fA))).hom p)).val
          map_one' := sorry
          map_mul' := sorry
          map_zero' := sorry
          map_add' := sorry })
      sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The diagonal `A' ⟶ A' ×_A A'`. -/
def doubleInl (fA : A' ⟶ A) : A' ⟶ doubleRing fA :=
  pullback.lift (𝟙 A') (𝟙 A') sorry

/-- The section `A' ⟶ A' ×_A A[I]` of the first projection. -/
def mixedInl (fA : A' ⟶ A) [RingHom.IsSquareZeroExtension fA.hom] :
    A' ⟶ mixedRing fA :=
  pullback.lift (𝟙 A') (fA ≫ trivSqZeroInl A (kernelObj fA)) sorry

/-- The structure morphism `Spec(A' ×_A A') ⟶ S`. -/
def specDouble (σA' : Spec A' ⟶ S) (fA : A' ⟶ A) :
    Spec (doubleRing fA) ⟶ S :=
  Spec.map (doubleInl fA) ≫ σA'

/-- The structure morphism `Spec(A' ×_A A[I]) ⟶ S`. -/
def specMixed (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    Spec (mixedRing fA) ⟶ S :=
  Spec.map (mixedInl fA) ≫ σA'

/-- Compatibility of `Spec.map` of the first double projection with `specDouble`. -/
theorem specDouble_fst_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A) :
    Spec.map (pullback.fst fA fA) ≫ specDouble σA' fA = σA' := sorry

/-- Compatibility of `Spec.map` of the second double projection with `specDouble`. -/
theorem specDouble_snd_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A) :
    Spec.map (pullback.snd fA fA) ≫ specDouble σA' fA = σA' := sorry

/-- Compatibility of `Spec.map` of the first mixed projection with `specMixed`. -/
theorem specMixed_fst_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    Spec.map (pullback.fst fA (trivSqZeroHom A (kernelObj fA))) ≫ specMixed σA' fA =
      σA' := sorry

/-- Compatibility of `Spec.map` of the second mixed projection with `specMixed`. -/
theorem specMixed_snd_comp (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    Spec.map (pullback.snd fA (trivSqZeroHom A (kernelObj fA))) ≫ specMixed σA' fA =
      specTrivSqZero σA (kernelObj fA) := sorry

/-- Compatibility of `doubleIsoMixed.inv` with the structure morphisms. -/
theorem doubleIsoMixed_inv_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    Spec.map (doubleIsoMixed fA).inv ≫ specMixed σA' fA = specDouble σA' fA := sorry

/-- Affine schemes are affine as left objects of `Over S`. -/
instance isAffine_overMkSpec {R : CommRingCat.{u}} {σ : Spec R ⟶ S} :
    IsAffine (Over.mk σ).left := sorry

/-- `Spec(A' ×_A A')` is affine as a left object of `Over S`. -/
instance isAffine_specDouble (σA' : Spec A' ⟶ S) (fA : A' ⟶ A) :
    IsAffine (Over.mk (specDouble σA' fA)).left :=
  isAffine_overMkSpec (σ := specDouble σA' fA)

/-- `Spec(A' ×_A A[I])` is affine as a left object of `Over S`. -/
instance isAffine_specMixed (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    [RingHom.IsSquareZeroExtension fA.hom] :
    IsAffine (Over.mk (specMixed σA' fA)).left :=
  isAffine_overMkSpec (σ := specMixed σA' fA)

/-- The first-order thickening `Spec(A) ⟶ Spec(A')` is a first-order thickening. -/
instance specOverHom_isFirstOrderThickening (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA)
    [RingHom.IsSquareZeroExtension fA.hom] :
    IsFirstOrderThickening (specOverHom fA hfA).left := sorry

/-- The trivial square-zero thickening `Spec(A) ⟶ Spec(A[I])` is a first-order
thickening. -/
instance specOverTriv_isFirstOrderThickening (σA : Spec A ⟶ S) (M : ModuleCat.{u} A) :
    IsFirstOrderThickening
      (specOverHom (trivSqZeroHom A M) (trivSqZeroHom_comp σA M)).left := sorry

/-- The affine pushout square of `Spec(A' ×_A A')` over `Spec(A)`. -/
theorem double_isPushout (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) :
    IsPushout (specOverHom fA hfA) (specOverHom fA hfA)
      (specOverHom (pullback.snd fA fA) (specDouble_snd_comp σA' fA))
      (specOverHom (pullback.fst fA fA) (specDouble_fst_comp σA' fA)) := sorry

/-- The affine pushout square of `Spec(A' ×_A A[I])` over `Spec(A)`. -/
theorem mixed_isPushout (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    IsPushout
      (specOverHom (trivSqZeroHom A (kernelObj fA)) (trivSqZeroHom_comp σA (kernelObj fA)))
      (specOverHom fA hfA)
      (specOverHom (pullback.snd fA (trivSqZeroHom A (kernelObj fA)))
        (specMixed_snd_comp σA σA' fA))
      (specOverHom (pullback.fst fA (trivSqZeroHom A (kernelObj fA)))
        (specMixed_fst_comp σA' fA)) := sorry

/-- The cartesian factor of `x'.hom` through the chosen reindexing of its codomain. -/
theorem liftReindex_isHomLift {x : X.p.Fiber (Over.mk σA)} (x' : liftCat x fA hfA) :
    X.p.IsHomLift (𝟙 (Over.mk σA) ≫ specOverHom fA hfA) x'.hom := sorry

/-- The chosen reindexing of the codomain of a lift along `A' ⟶ A` is isomorphic to
`x`. -/
def liftReindexIso {A'' : CommRingCat.{u}} {σA'' : Spec A'' ⟶ S}
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
def infPair {x : X.p.Fiber (Over.mk σA)} (x' : liftCat x fA hfA)
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
def infPairHom {x : X.p.Fiber (Over.mk σA)} (x' : liftCat x fA hfA)
    (e : Aut x'.codomain) :
    infPair x' (1 : Aut x'.codomain) ⟶ infPair x' e where
  fst := 𝟙 x'.codomain
  snd := e.hom
  w := sorry

/-- The (RS*) restriction comparison along the double pullback of a thickening. -/
def doubleComparison (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) :
    X.p.Fiber (Over.mk (specDouble σA' fA)) ⥤
      (Chosen.reindex X.p (specOverHom fA hfA)) ⊡
        (Chosen.reindex X.p (specOverHom fA hfA)) :=
  restrictionComparison X.p (double_isPushout σA' fA hfA).w

/-- The (RS*) restriction comparison along the mixed pullback `A' ×_A A[I]`. -/
def mixedComparison (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    X.p.Fiber (Over.mk (specMixed σA' fA)) ⥤
      (Chosen.reindex X.p (specOverHom fA hfA)) ⊡
        (Chosen.reindex X.p
          (specOverHom (trivSqZeroHom A (kernelObj fA))
            (trivSqZeroHom_comp σA (kernelObj fA)))) :=
  restrictionComparison X.p (mixed_isPushout σA σA' fA hfA).w

/-- Inverse of `doubleComparison`, using the (RS*) equivalence instance. -/
def doubleComparisonInv (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) :
    ((Chosen.reindex X.p (specOverHom fA hfA)) ⊡
      (Chosen.reindex X.p (specOverHom fA hfA))) ⥤
        X.p.Fiber (Over.mk (specDouble σA' fA)) :=
  @Functor.inv _ _ _ _ (doubleComparison σA' fA hfA) sorry

/-- Inverse of `mixedComparison`, using the (RS*) equivalence instance. -/
def mixedComparisonInv (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    ((Chosen.reindex X.p (specOverHom fA hfA)) ⊡
      (Chosen.reindex X.p
        (specOverHom (trivSqZeroHom A (kernelObj fA))
          (trivSqZeroHom_comp σA (kernelObj fA))))) ⥤
        X.p.Fiber (Over.mk (specMixed σA' fA)) :=
  @Functor.inv _ _ _ _ (mixedComparison σA σA' fA hfA) sorry

/-- Pair two lifts of `x` along `A' ⟶ A` as an object of the 2-fibre product of
restriction. -/
def liftsPair {x : X.p.Fiber (Over.mk σA)} (a b : liftCat x fA hfA) :
    (Chosen.reindex X.p (specOverHom fA hfA)) ⊡
      (Chosen.reindex X.p (specOverHom fA hfA)) where
  fst := a.codomain
  snd := b.codomain
  iso := (liftReindexIso a).trans (liftReindexIso b).symm

/-- Pair a lift along `A' ⟶ A` with a lift along `A[I] ⟶ A`. -/
def mixPair {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (i : liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA))) :
    (Chosen.reindex X.p (specOverHom fA hfA)) ⊡
      (Chosen.reindex X.p
        (specOverHom (trivSqZeroHom A (kernelObj fA))
          (trivSqZeroHom_comp σA (kernelObj fA)))) where
  fst := a.codomain
  snd := i.codomain
  iso := (liftReindexIso a).trans (liftReindexIso i).symm

/-- The fibre object over `Spec(A' ×_A A')` associated to a pair of lifts by
(RS*). -/
def pairFiber {x : X.p.Fiber (Over.mk σA)} (a b : liftCat x fA hfA) :
    X.p.Fiber (Over.mk (specDouble σA' fA)) :=
  (doubleComparisonInv σA' fA hfA).obj (liftsPair a b)

/-- The fibre object over `Spec(A' ×_A A[I])` associated to a mixed pair of lifts
by (RS*). -/
def mixFiber {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (i : liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA))) :
    X.p.Fiber (Over.mk (specMixed σA' fA)) :=
  (mixedComparisonInv σA σA' fA hfA).obj (mixPair a i)

/-- Transport a mixed fibre object to the double pullback along
`A' ×_A A' ≅ A' ×_A A[I]`. -/
def transportMixed (y : X.p.Fiber (Over.mk (specMixed σA' fA))) :
    X.p.Fiber (Over.mk (specDouble σA' fA)) :=
  Chosen.reindexObj X.p
    (specOverHom (doubleIsoMixed fA).inv (doubleIsoMixed_inv_comp σA' fA)) y

/-- Restrict a double fibre object along the second projection `A' ×_A A' ⟶ A'`. -/
def restrictDoubleSnd (y : X.p.Fiber (Over.mk (specDouble σA' fA))) :
    X.p.Fiber (Over.mk σA') :=
  Chosen.reindexObj X.p
    (specOverHom (pullback.snd fA fA) (specDouble_snd_comp σA' fA)) y

/-- Restrict a mixed fibre object along `A' ×_A A[I] ⟶ A[I]`. -/
def restrictMixedSnd (y : X.p.Fiber (Over.mk (specMixed σA' fA))) :
    X.p.Fiber (Over.mk (specTrivSqZero σA (kernelObj fA))) :=
  Chosen.reindexObj X.p
    (specOverHom (pullback.snd fA (trivSqZeroHom A (kernelObj fA)))
      (specMixed_snd_comp σA σA' fA)) y

/-- Package a fibre object over `Spec(A')` as a lift of its reindexing along
`Spec(A') ⟶ Spec(A)`. -/
def liftOfFiber (y : X.p.Fiber (Over.mk σA')) :
    liftCat (Chosen.reindexObj X.p (specOverHom fA hfA) y) fA hfA :=
  @UnderLift.ofHom _ _ _ _ X.p _ _ _
    (Chosen.reindexObj X.p (specOverHom fA hfA) y) _
    (Chosen.cartesianHom X.p (specOverHom fA hfA) y)
    (Chosen.cartesianHom.isHomLift X.p (specOverHom fA hfA) y)

/-- The (RS*) combination of a lift of `x` with a lift to `A[I]` restricts to `x`. -/
theorem combineLift_reindex {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (i : liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA))) :
    Chosen.reindexObj X.p (specOverHom fA hfA)
      (restrictDoubleSnd (transportMixed (mixFiber a i))) = x := sorry

/-- Combine a lift along `A' ⟶ A` with a lift along `A[I] ⟶ A` by the (RS*)
equivalence through `A' ×_A A[I] ≅ A' ×_A A'`. -/
def combineLift {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (i : liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA))) :
    liftCat x fA hfA :=
  combineLift_reindex a i ▸
    liftOfFiber (restrictDoubleSnd (transportMixed (mixFiber a i)))

/-- Twist the trivial deformation lift by an infinitesimal automorphism. -/
theorem twistTrivial_isHomLift {x : X.p.Fiber (Over.mk σA)}
    (α : infType x (kernelObj fA)) :
    X.p.IsHomLift
      (specOverHom (trivSqZeroHom A (kernelObj fA))
        (trivSqZeroHom_comp σA (kernelObj fA)))
      ((trivialDeformationLift x (kernelObj fA)).hom ≫
        Fiber.fiberInclusion.map α.val.hom) := sorry

/-- The trivial deformation of `x` to `A[I]`, twisted by an element of
`Inf(x'_I/x)`. -/
def twistTrivial {x : X.p.Fiber (Over.mk σA)} (α : infType x (kernelObj fA)) :
    liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA)) :=
  @UnderLift.ofHom _ _ _ _ X.p _ _ _ x _
    ((trivialDeformationLift x (kernelObj fA)).hom ≫
      Fiber.fiberInclusion.map α.val.hom)
    (twistTrivial_isHomLift α)

/-- The (RS*) mixed pair morphism with identity on `x'` and an infinitesimal
automorphism of the trivial deformation on the second factor. -/
def mixPairHom {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (α : infType x (kernelObj fA)) :
    mixPair a (trivialDeformationLift x (kernelObj fA)) ⟶ mixPair a (twistTrivial α) where
  fst := 𝟙 a.codomain
  snd := α.val.hom
  w := sorry

/-- Restricting the (RS*) mixed pairing of `x'` with the trivial deformation along
the first projection recovers `x'`. -/
theorem mixPair_fst_eq {x : X.p.Fiber (Over.mk σA)} (x' : liftCat x fA hfA)
    (i : liftCat x (trivSqZeroHom A (kernelObj fA))
      (trivSqZeroHom_comp σA (kernelObj fA))) :
    ((doubleComparison σA' fA hfA).obj
      (transportMixed (mixFiber x' i))).fst = x'.codomain := sorry

/-- The reverse (RS*) mixed pair morphism associated to an infinitesimal
automorphism of the trivial deformation. -/
def mixPairHomInv {x : X.p.Fiber (Over.mk σA)} (a : liftCat x fA hfA)
    (α : infType x (kernelObj fA)) :
    mixPair a (twistTrivial α) ⟶ mixPair a (trivialDeformationLift x (kernelObj fA)) where
  fst := 𝟙 a.codomain
  snd := α.val.inv
  w := sorry

/-- The (RS*) automorphism of `x'` associated to an infinitesimal automorphism of
the trivial deformation. -/
def infCompareAut (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
    (α : infType x (kernelObj fA)) : Aut x'.codomain :=
  let χ := (doubleComparison σA' fA hfA).map
    (Chosen.reindexMap X.p
      (specOverHom (doubleIsoMixed fA).inv (doubleIsoMixed_inv_comp σA' fA))
      ((mixedComparisonInv σA σA' fA hfA).map (mixPairHom x' α)))
  let χinv := (doubleComparison σA' fA hfA).map
    (Chosen.reindexMap X.p
      (specOverHom (doubleIsoMixed fA).inv (doubleIsoMixed_inv_comp σA' fA))
      ((mixedComparisonInv σA σA' fA hfA).map (mixPairHomInv x' α)))
  Fiber.isoMk
    { hom :=
        eqToHom (congrArg Subtype.val
            (mixPair_fst_eq x' (trivialDeformationLift x (kernelObj fA)))).symm ≫
          Fiber.fiberInclusion.map χ.fst ≫
            eqToHom (congrArg Subtype.val (mixPair_fst_eq x' (twistTrivial α)))
      inv :=
        eqToHom (congrArg Subtype.val (mixPair_fst_eq x' (twistTrivial α))).symm ≫
          Fiber.fiberInclusion.map χinv.fst ≫
            eqToHom (congrArg Subtype.val
              (mixPair_fst_eq x' (trivialDeformationLift x (kernelObj fA))))
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

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
instance infinitesimalAut.instAddCommGroup {x : X.p.Fiber (Over.mk σA)}
    (x' : liftCat x fA hfA) : AddCommGroup (infinitesimalAut x') where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  neg_add_cancel := sorry
  zsmul := zsmulRec
  add_comm := sorry

/-- Compatibility of `doubleIsoMixed.hom` with the structure morphisms. -/
theorem doubleIsoMixed_hom_comp (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) [RingHom.IsSquareZeroExtension fA.hom] :
    Spec.map (doubleIsoMixed fA).hom ≫ specDouble σA' fA = specMixed σA' fA := sorry

/-- Restricting the (RS*) double pairing of a fibre automorphism of `x'` along
`A' ×_A A[I] ⟶ A[I]` recovers the trivial deformation of `x`. -/
theorem infPair_snd_eq (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
    (e : Aut x'.codomain) :
    restrictMixedSnd
        (Chosen.reindexObj X.p
          (specOverHom (doubleIsoMixed fA).hom (doubleIsoMixed_hom_comp σA' fA hfA))
          ((doubleComparisonInv σA' fA hfA).obj (infPair x' e))) =
      trivialDeformation x (kernelObj fA) := sorry

/-- Conjugate a fibre morphism over `Spec(A[I])` to an automorphism of the trivial
deformation. -/
def infIsoInvAut (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
    (β : infinitesimalAut x') : Aut (trivialDeformation x (kernelObj fA)) :=
  let ψ := Chosen.reindexMap X.p
    (specOverHom (pullback.snd fA (trivSqZeroHom A (kernelObj fA)))
      (specMixed_snd_comp σA σA' fA))
    (Chosen.reindexMap X.p
      (specOverHom (doubleIsoMixed fA).hom (doubleIsoMixed_hom_comp σA' fA hfA))
      ((doubleComparisonInv σA' fA hfA).map (infPairHom x' β.val)))
  let ψinv := Chosen.reindexMap X.p
    (specOverHom (pullback.snd fA (trivSqZeroHom A (kernelObj fA)))
      (specMixed_snd_comp σA σA' fA))
    (Chosen.reindexMap X.p
      (specOverHom (doubleIsoMixed fA).hom (doubleIsoMixed_hom_comp σA' fA hfA))
      ((doubleComparisonInv σA' fA hfA).map
        { fst := 𝟙 x'.codomain
          snd := (β.val).inv
          w := sorry }))
  Fiber.isoMk
    { hom :=
        eqToHom (congrArg Subtype.val (infPair_snd_eq x x' (1 : Aut x'.codomain))).symm ≫
          Fiber.fiberInclusion.map ψ ≫
            eqToHom (congrArg Subtype.val (infPair_snd_eq x x' β.val))
      inv :=
        eqToHom (congrArg Subtype.val (infPair_snd_eq x x' β.val)).symm ≫
          Fiber.fiberInclusion.map ψinv ≫
            eqToHom (congrArg Subtype.val (infPair_snd_eq x x' (1 : Aut x'.codomain)))
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- The reverse (RS*) difference `Inf(x'/x) → Inf_x(I)`. -/
def infIsoInv (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
    (β : infinitesimalAut x') : (infFunctor x).obj (kernelObj fA) :=
  ⟨infIsoInvAut x x' β, sorry⟩

/-- The forward comparison `Inf_x(I) → Inf(x'/x)` of the (RS*) difference pairing. -/
def infIsoHom (x : X.p.Fiber (Over.mk σA)) (x' : liftCat x fA hfA)
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
    (infIso x x').hom α = infIsoHom x x' α := sorry

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

/-- The action of `T_x(I)` on a nonempty set of lifts is simply transitive. -/
theorem tangentAction_simplyTransitive (x : X.p.Fiber (Over.mk σA))
    [Nonempty (lifts x fA hfA)] (ξ η : lifts x fA hfA) :
    ∃! t : (tangentFunctor x).obj (kernelObj fA), tangentAction x t ξ = η := sorry

end AlgebraicGeometry.GroupoidsOver
