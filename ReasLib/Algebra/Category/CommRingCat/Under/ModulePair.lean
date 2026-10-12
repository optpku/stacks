/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct ZeroObject

universe u

/-- Morphisms between an algebra-module pair `(B, N)` and `(B', N')`. -/
structure ModulePair.Map {A : CommRingCat.{u}} (B : Under A) (N : ModuleCat.{u} B.right)
    (B' : Under A) (N' : ModuleCat.{u} B'.right) where
  /-- The morphism of `A`-algebras. -/
  base : B ⟶ B'
  /-- The map of modules, semilinear over the map of algebras. -/
  linear : N →ₛₗ[base.right.hom] N'

namespace ModulePair.Map

variable {A : CommRingCat.{u}} {B B' B'' : Under A}
variable {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
variable {N'' : ModuleCat.{u} B''.right}

/-- The identity morphism of an algebra-module pair. -/
def id (B : Under A) (N : ModuleCat.{u} B.right) : ModulePair.Map B N B N where
  base := 𝟙 B
  linear := LinearMap.id

/-- The linear part of the identity pair morphism is the identity on elements. -/
theorem id_apply (B : Under A) (N : ModuleCat.{u} B.right) (x : N) :
    (id B N).linear x = x := sorry

/-- A linear map at a fixed algebra gives a morphism of algebra-module pairs. -/
def ofLinear {B : Under A} {N N' : ModuleCat.{u} B.right} (f : N ⟶ N') :
    ModulePair.Map B N B N' where
  base := 𝟙 B
  linear := {
    toFun := f
    map_add' := f.hom.map_add
    map_smul' := f.hom.map_smul }

/-- The linear part of a fixed-base pair morphism is the original linear map. -/
theorem ofLinear_apply {B : Under A} {N N' : ModuleCat.{u} B.right}
    (f : N ⟶ N') (x : N) : (ofLinear f).linear x = f x := sorry

/-- The linear part of a composite pair morphism is semilinear over the composite base map. -/
theorem comp_map_add (f : ModulePair.Map B N B' N') (g : ModulePair.Map B' N' B'' N'')
    (x y : N) :
    g.linear (f.linear (x + y)) = g.linear (f.linear x) + g.linear (f.linear y) := sorry

/-- The linear part of a composite pair morphism is semilinear over the composite base map. -/
theorem comp_map_smul (f : ModulePair.Map B N B' N') (g : ModulePair.Map B' N' B'' N'')
    (b : B.right) (x : N) :
    g.linear (f.linear (b • x)) = (f.base ≫ g.base).right.hom b • g.linear (f.linear x) := sorry

/-- Composition of morphisms of algebra-module pairs. -/
def comp (f : ModulePair.Map B N B' N') (g : ModulePair.Map B' N' B'' N'') :
    ModulePair.Map B N B'' N'' where
  base := f.base ≫ g.base
  linear := {
    toFun := fun x => g.linear (f.linear x)
    map_add' := comp_map_add f g
    map_smul' := comp_map_smul f g }

/-- The base map of a composite pair morphism is the composite base map. -/
theorem comp_base (f : ModulePair.Map B N B' N') (g : ModulePair.Map B' N' B'' N'') :
    (comp f g).base = f.base ≫ g.base := sorry

/-- The linear map of a composite pair morphism is pointwise composition. -/
theorem comp_linear (f : ModulePair.Map B N B' N') (g : ModulePair.Map B' N' B'' N'')
    (x : N) : (comp f g).linear x = g.linear (f.linear x) := sorry

end ModulePair.Map

/-- A functorial construction on algebra-module pairs, expressed using semilinear transition maps. -/
structure ModulePairFunctor (A : CommRingCat.{u}) where
  /-- The module assigned to `(B, N)`. -/
  obj (B : Under A) (N : ModuleCat.{u} B.right) : ModuleCat.{u} B.right
  /-- The semilinear transition map assigned to a morphism of pairs. -/
  map {B B' : Under A} {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') : obj B N →ₛₗ[f.base.right.hom] obj B' N'
  /-- The identity pair morphism acts identically. -/
  map_id (B : Under A) (N : ModuleCat.{u} B.right) (x : obj B N) :
    map (ModulePair.Map.id B N) x = x
  /-- Pair morphism composition acts by composition. -/
  map_comp {B B' B'' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} {N'' : ModuleCat.{u} B''.right}
    (f : ModulePair.Map B N B' N') (g : ModulePair.Map B' N' B'' N'') (x : obj B N) :
    map (ModulePair.Map.comp f g) x = map g (map f x)

namespace ModulePairFunctor

variable {A : CommRingCat.{u}}

/-- The fixed-base map is linear over the unchanged base algebra. -/
theorem atMap_smul (T : ModulePairFunctor A) {B : Under A}
    {N N' : ModuleCat.{u} B.right} (f : N ⟶ N') (b : B.right) (x : T.obj B N) :
    T.map (ModulePair.Map.ofLinear f) (b • x) =
      b • T.map (ModulePair.Map.ofLinear f) x := sorry

/-- The fixed-base map underlying a functor on algebra-module pairs. -/
def atMap (T : ModulePairFunctor A) {B : Under A} {N N' : ModuleCat.{u} B.right}
    (f : N ⟶ N') : T.obj B N ⟶ T.obj B N' :=
  ModuleCat.ofHom {
    toFun := T.map (ModulePair.Map.ofLinear f)
    map_add' := (T.map (ModulePair.Map.ofLinear f)).map_add
    map_smul' := atMap_smul T f }

/-- The fixed-base maps preserve identities. -/
theorem atMap_id (T : ModulePairFunctor A) (B : Under A) (N : ModuleCat.{u} B.right) :
    T.atMap (𝟙 N) = 𝟙 (T.obj B N) := sorry

/-- The fixed-base maps preserve composition. -/
theorem atMap_comp (T : ModulePairFunctor A) {B : Under A}
    {N N' N'' : ModuleCat.{u} B.right} (f : N ⟶ N') (g : N' ⟶ N'') :
    T.atMap (f ≫ g) = T.atMap f ≫ T.atMap g := sorry

/-- Restriction of a pair functor to modules over one fixed algebra. -/
def fixedBase (T : ModulePairFunctor A) (B : Under A) :
    ModuleCat.{u} B.right ⥤ ModuleCat.{u} B.right where
  obj N := T.obj B N
  map f := T.atMap f
  map_id N := T.atMap_id B N
  map_comp f g := T.atMap_comp f g

/-- Objects of the fixed-base functor are the corresponding pair-functor objects. -/
theorem fixedBase_obj (T : ModulePairFunctor A) (B : Under A) (N : ModuleCat.{u} B.right) :
    (T.fixedBase B).obj N = T.obj B N := sorry

/-- Morphisms of the fixed-base functor are the corresponding fixed-base maps. -/
theorem fixedBase_map (T : ModulePairFunctor A) (B : Under A)
    {N N' : ModuleCat.{u} B.right} (f : N ⟶ N') :
    (T.fixedBase B).map f = T.atMap f := sorry

/-- A natural family of module maps between functors on algebra-module pairs. -/
structure Hom (T U : ModulePairFunctor A) where
  /-- The component at an algebra-module pair. -/
  app (B : Under A) (N : ModuleCat.{u} B.right) : T.obj B N ⟶ U.obj B N
  /-- Naturality with respect to simultaneous changes of algebra and module. -/
  naturality {B B' : Under A} {N : ModuleCat.{u} B.right} {N' : ModuleCat.{u} B'.right}
    (f : ModulePair.Map B N B' N') (x : T.obj B N) :
    U.map f (app B N x) = app B' N' (T.map f x)

namespace Hom

variable {T U : ModulePairFunctor A}

/-- Construct a natural family of module maps from its components and naturality equations. -/
def ofComponents
    (app : (B : Under A) → (N : ModuleCat.{u} B.right) → T.obj B N ⟶ U.obj B N)
    (naturality : ∀ {B B' : Under A} {N : ModuleCat.{u} B.right}
      {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N') (x : T.obj B N),
      U.map f (app B N x) = app B' N' (T.map f x)) : Hom T U where
  app := app
  naturality := naturality

end Hom

end ModulePairFunctor

namespace ModulePair

variable {A : CommRingCat.{u}}

/-- The canonical right action of a commutative ring on one of its modules. -/
instance instModuleMulOpposite (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    Module Rᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id R).fromOpposite fun x y => mul_comm x y)

/-- The canonical left and right actions of a commutative ring on a module agree. -/
theorem opposite_smul_eq_smul (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (r : R) (x : M) : MulOpposite.op r • x = r • x := sorry

/-- The canonical left and right actions of a commutative ring on a module agree. -/
instance instIsCentralScalar (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    IsCentralScalar R M where
  op_smul_eq_smul := opposite_smul_eq_smul R M

/-- The trivial square-zero extension `B[N]`, regarded as an `A`-algebra. -/
def squareZero (B : Under A) (N : ModuleCat.{u} B.right) : Under A :=
  Under.mk (CommRingCat.ofHom <|
    (TrivSqZeroExt.inlHom B.right N).comp B.hom.hom)

/-- The square-zero extension has the expected underlying commutative ring. -/
theorem squareZero_right (B : Under A) (N : ModuleCat.{u} B.right) :
    (squareZero B N).right = CommRingCat.of (TrivSqZeroExt B.right N) := sorry

/-- The canonical inclusion `B ⟶ B[N]`. -/
theorem inclusion_commutes (B : Under A) (N : ModuleCat.{u} B.right) :
    B.hom ≫ CommRingCat.ofHom (TrivSqZeroExt.inlHom B.right N) = (squareZero B N).hom := sorry

/-- The canonical inclusion `B ⟶ B[N]`. -/
def inclusion (B : Under A) (N : ModuleCat.{u} B.right) : B ⟶ squareZero B N :=
  Under.homMk (CommRingCat.ofHom (TrivSqZeroExt.inlHom B.right N))
    (inclusion_commutes B N)

/-- The canonical projection `B[N] ⟶ B`. -/
theorem projection_commutes (B : Under A) (N : ModuleCat.{u} B.right) :
    (squareZero B N).hom ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom B.right B.right N) =
      B.hom := sorry

/-- The canonical projection `B[N] ⟶ B`. -/
def projection (B : Under A) (N : ModuleCat.{u} B.right) : squareZero B N ⟶ B :=
  Under.homMk (CommRingCat.ofHom (TrivSqZeroExt.fstHom B.right B.right N))
    (projection_commutes B N)

/-- The projection of a square-zero extension retracts its canonical inclusion. -/
theorem inclusion_projection (B : Under A) (N : ModuleCat.{u} B.right) :
    inclusion B N ≫ projection B N = 𝟙 B := sorry

/-- The underlying function of the square-zero map associated to a pair morphism. -/
def squareZeroMapFun {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N')
    (x : TrivSqZeroExt B.right N) : TrivSqZeroExt B'.right N' :=
  (f.base.right x.1, f.linear x.2)

/-- The square-zero map preserves zero. -/
theorem squareZeroMap_zero {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N') :
    squareZeroMapFun f 0 = 0 := sorry

/-- The square-zero map preserves one. -/
theorem squareZeroMap_one {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N') :
    squareZeroMapFun f 1 = 1 := sorry

/-- The square-zero map preserves addition. -/
theorem squareZeroMap_add {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N')
    (x y : TrivSqZeroExt B.right N) :
    squareZeroMapFun f (x + y) = squareZeroMapFun f x + squareZeroMapFun f y := sorry

/-- The square-zero map preserves multiplication. -/
theorem squareZeroMap_mul {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N')
    (x y : TrivSqZeroExt B.right N) :
    squareZeroMapFun f (x * y) = squareZeroMapFun f x * squareZeroMapFun f y := sorry

/-- The ring homomorphism on square-zero extensions induced by a pair morphism. -/
def squareZeroRingHom {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N') :
    TrivSqZeroExt B.right N →+* TrivSqZeroExt B'.right N' where
  toFun := squareZeroMapFun f
  map_zero' := squareZeroMap_zero f
  map_one' := squareZeroMap_one f
  map_add' := squareZeroMap_add f
  map_mul' := squareZeroMap_mul f

/-- The square-zero ring homomorphism acts componentwise. -/
theorem squareZeroRingHom_apply {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N')
    (x : TrivSqZeroExt B.right N) :
    squareZeroRingHom f x = (f.base.right x.1, f.linear x.2) := sorry

/-- The square-zero ring homomorphism commutes with the structural maps from `A`. -/
theorem squareZeroRingHom_commutes {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N') :
    (squareZero B N).hom ≫ CommRingCat.ofHom (squareZeroRingHom f) =
      (squareZero B' N').hom := sorry

/-- The morphism of square-zero `A`-algebras induced by a pair morphism. -/
def map {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N') :
    squareZero B N ⟶ squareZero B' N' :=
  Under.homMk (CommRingCat.ofHom (squareZeroRingHom f)) (squareZeroRingHom_commutes f)

/-- Square-zero pair maps commute with the canonical inclusions. -/
theorem map_inclusion {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N') :
    inclusion B N ≫ map f = f.base ≫ inclusion B' N' := sorry

/-- Square-zero pair maps commute with the canonical projections. -/
theorem projection_map {B B' : Under A} {N : ModuleCat.{u} B.right}
    {N' : ModuleCat.{u} B'.right} (f : ModulePair.Map B N B' N') :
    map f ≫ projection B' N' = projection B N ≫ f.base := sorry

end ModulePair
