/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Quadruple
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemePullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Quadruple
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.FiniteDegreeCover

/-! # The graded algebra pulled back from an algebraic space to a scheme -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules SheafOfModules.RingedSite
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
/-- The Type `u` pullback of an unlifted degree piece along a morphism from a scheme. -/
abbrev pullbackDegree {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (n : ℕ) : Z.left.Modules :=
  Modules.pullbackToScheme g (deg.obj n)

/-- `pullbackDegree g deg n` is the scheme-chart restriction of the pulled-back degree-`n`
piece. -/
theorem pullbackDegree_eq {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (n : ℕ) :
    pullbackDegree g deg n = Modules.pullbackToScheme g (deg.obj n) :=
  rfl

/-- The Type `u` graded pieces of `g^* 𝒜` on `Z.left`: pulled-back nonnegative degree
pieces, and the zero module in negative degrees. -/
def pullbackAlgebraObj {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (n : ℤ) : Z.left.Modules :=
  match n with
  | Int.ofNat k => pullbackDegree g deg k
  | Int.negSucc _ =>
      (0 : Z.left.Modules)

/-- Nonnegative components of `pullbackAlgebraObj` are `pullbackDegree`. -/
theorem pullbackAlgebraObj_ofNat {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (n : ℕ) :
    pullbackAlgebraObj g deg (Int.ofNat n) = pullbackDegree g deg n :=
  rfl

/-- Negative components of `pullbackAlgebraObj` are the zero module. -/
theorem pullbackAlgebraObj_negSucc {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (n : ℕ) :
    pullbackAlgebraObj g deg (Int.negSucc n) =
      (0 : Z.left.Modules) :=
  rfl

/-- The canonical map `g^* 𝒪_X ⟶ g^* 𝒜_0` obtained by pulling back the degree-zero unit. -/
def pullbackDegreeZeroUnit {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜) :
    (Modules.restrictToScheme Z).obj (SheafOfModules.unit (structureSheaf (ofOver Z))) ⟶
      pullbackDegree g deg 0 :=
  (Modules.restrictToScheme Z).map
    (Modules.structureModulePullbackInv g ≫
      (Modules.pullback g).map (degreeZeroUnit deg))

/-- `pullbackDegreeZeroUnit` is restriction of the pulled-back degree-zero unit. -/
theorem pullbackDegreeZeroUnit_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) :
    pullbackDegreeZeroUnit g deg =
      (Modules.restrictToScheme Z).map
        (Modules.structureModulePullbackInv g ≫
          (Modules.pullback g).map (degreeZeroUnit deg)) :=
  rfl

/-- The unlifted multiplication of pulled-back degree pieces, before restriction to `Z.left`. -/
def pullbackDegreeMul {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (i j : ℕ) :
    (Modules.pullback g).obj (deg.obj i) ⊗ (Modules.pullback g).obj (deg.obj j) ⟶
      (Modules.pullback g).obj (deg.obj (i + j)) :=
  pullbackTensorLax g (deg.obj i) (deg.obj j) ≫
    (Modules.pullback g).map (deg.mul i j)

/-- `pullbackDegreeMul` is the laxator followed by the pullback of `deg.mul`. -/
theorem pullbackDegreeMul_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (i j : ℕ) :
    pullbackDegreeMul g deg i j =
      pullbackTensorLax g (deg.obj i) (deg.obj j) ≫
        (Modules.pullback g).map (deg.mul i j) :=
  rfl

/-- Restriction of `pullbackDegreeMul` to the underlying scheme of `Z`. -/
def pullbackDegreeMulToScheme {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (i j : ℕ) :
    (Modules.restrictToScheme Z).obj
        ((Modules.pullback g).obj (deg.obj i) ⊗
          (Modules.pullback g).obj (deg.obj j)) ⟶
      pullbackDegree g deg (i + j) :=
  (Modules.restrictToScheme Z).map (pullbackDegreeMul g deg i j)

/-- `pullbackDegreeMulToScheme` is `restrictToScheme` of `pullbackDegreeMul`. -/
theorem pullbackDegreeMulToScheme_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (i j : ℕ) :
    pullbackDegreeMulToScheme g deg i j =
      (Modules.restrictToScheme Z).map (pullbackDegreeMul g deg i j) :=
  rfl

/-- The unit section of `𝒪_Z` as a section of the scheme-level unit module. -/
private def schemeUnitOne {Z : Over S} (U : (Z.left.Opens)ᵒᵖ) :
    (SheafOfModules.unit Z.left.ringCatSheaf).val.obj U :=
  (1 : Z.left.ringCatSheaf.obj.obj U)

/-- `schemeUnitOne` is the unit of the structure sheaf of `Z.left`. -/
private theorem schemeUnitOne_eq {Z : Over S} (U : (Z.left.Opens)ᵒᵖ) :
    schemeUnitOne (Z := Z) U = (1 : Z.left.ringCatSheaf.obj.obj U) :=
  rfl

/-- The actual unit comparison for restriction to the represented scheme. -/
def schemeUnitToRestrictUnit {Z : Over S} :
    SheafOfModules.unit Z.left.ringCatSheaf ⟶
      (Modules.restrictToScheme Z).obj
        (SheafOfModules.unit (structureSheaf (ofOver Z))) :=
  Modules.RestrictToScheme.unitMap Z

/-- The unit map is the composite of the canonical site/scalar restriction unit maps. -/
theorem schemeUnitToRestrictUnit_apply {Z : Over S} (U : (Z.left.Opens)ᵒᵖ)
    (x : (SheafOfModules.unit Z.left.ringCatSheaf).val.obj U) :
    ((schemeUnitToRestrictUnit (Z := Z)).val.app U).hom x =
      ((Modules.RestrictToScheme.unitMap Z).val.app U).hom x := rfl

/-- The degree-zero unit section of `g^* 𝒜`, obtained by applying `pullbackDegreeZeroUnit`
to the image of `1`. -/
@[no_expose] def pullbackAlgebraOne {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (U : (Z.left.Opens)ᵒᵖ) :
    (pullbackAlgebraObj g deg 0).val.obj U :=
  ((pullbackDegreeZeroUnit g deg).val.app U).hom
    (((schemeUnitToRestrictUnit (Z := Z)).val.app U).hom (schemeUnitOne (Z := Z) U))

/-- The scheme-level multiplication of pulled-back nonnegative degree pieces, as a
morphism out of the tensor product of `pullbackDegree` modules. -/
def pullbackDegreeMulScheme {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (i j : ℕ) :
    pullbackDegree g deg i ⊗ pullbackDegree g deg j ⟶ pullbackDegree g deg (i + j) :=
  Modules.restrictTensorLax ((Modules.pullback g).obj (deg.obj i))
      ((Modules.pullback g).obj (deg.obj j)) ≫
    (Modules.restrictToScheme Z).map (pullbackDegreeMul g deg i j)

/-- `pullbackDegreeMulScheme` is the restriction tensor comparison followed by restriction of
`pullbackDegreeMul`. -/
theorem pullbackDegreeMulScheme_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (i j : ℕ) :
    pullbackDegreeMulScheme g deg i j =
      Modules.restrictTensorLax ((Modules.pullback g).obj (deg.obj i))
          ((Modules.pullback g).obj (deg.obj j)) ≫
        (Modules.restrictToScheme Z).map (pullbackDegreeMul g deg i j) :=
  rfl

/-- Sectionwise multiplication of nonnegative pulled-back degree pieces, induced by
`pullbackDegreeMul` / `deg.mul`. -/
def pullbackDegreeMulBilinear {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (U : (Z.left.Opens)ᵒᵖ) (i j : ℕ) :
    (pullbackDegree g deg i).val.obj U →ₗ[Z.left.sheaf.obj.obj U]
      (pullbackDegree g deg j).val.obj U →ₗ[Z.left.sheaf.obj.obj U]
        (pullbackDegree g deg (i + j)).val.obj U :=
  by
    let A := (pullbackDegree g deg i).val.obj U
    let B := (pullbackDegree g deg j).val.obj U
    let f := fun (x : A) (y : B) ↦
      ((pullbackDegreeMulScheme g deg i j).val.app U).hom
        (SheafOfModules.RingedSite.tensorSection Z.left.sheaf U x y)
    have laws :
        (∀ (x x' : A) (y : B), f (x + x') y = f x y + f x' y) ∧
        (∀ (r : Z.left.sheaf.obj.obj U) (x : A) (y : B), f (r • x) y = r • f x y) ∧
        (∀ (x : A) (y y' : B), f x (y + y') = f x y + f x y') ∧
        (∀ (r : Z.left.sheaf.obj.obj U) (x : A) (y : B), f x (r • y) = r • f x y) := by sorry
    exact LinearMap.mk₂ _ f laws.1 laws.2.1 laws.2.2.1 laws.2.2.2

/-- `pullbackDegreeMulBilinear` evaluates by applying `pullbackDegreeMulScheme` to a pure
tensor section. -/
theorem pullbackDegreeMulBilinear_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (U : (Z.left.Opens)ᵒᵖ) (i j : ℕ)
    (x : (pullbackDegree g deg i).val.obj U)
    (y : (pullbackDegree g deg j).val.obj U) :
    pullbackDegreeMulBilinear g deg U i j x y =
      ((pullbackDegreeMulScheme g deg i j).val.app U).hom
        (SheafOfModules.RingedSite.tensorSection Z.left.sheaf U x y) :=
  sorry

/-- Sectionwise multiplication of homogeneous pieces of `g^* 𝒜`. Nonnegative degrees use
`pullbackDegreeMul` / `deg.mul`; if either degree is negative the source is the zero
module and the map is zero. -/
def pullbackAlgebraMul {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (U : (Z.left.Opens)ᵒᵖ) (n m : ℤ) :
    (pullbackAlgebraObj g deg n).val.obj U →ₗ[Z.left.sheaf.obj.obj U]
      (pullbackAlgebraObj g deg m).val.obj U →ₗ[Z.left.sheaf.obj.obj U]
        (pullbackAlgebraObj g deg (n + m)).val.obj U :=
  match n, m with
  | Int.ofNat i, Int.ofNat j => pullbackDegreeMulBilinear g deg U i j
  | _, _ => 0

/-- The Type `u` graded algebra `g^* 𝒜` on `Z.left`, assembled from `pullbackDegree`. -/
def pullbackAlgebra {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜) :
    GradedAlgebraSheaf.{u, u} Z.left.sheaf := by
  let obj := pullbackAlgebraObj g deg
  let one := pullbackAlgebraOne g deg
  let mul := pullbackAlgebraMul g deg
  have laws :
    (∀ {U V : Z.left.Opensᵒᵖ} (f : U ⟶ V),
      ((obj 0).val.map f).hom (one U) = one V) ∧
    (∀ {U V : Z.left.Opensᵒᵖ} (f : U ⟶ V) (n m : ℤ)
      (a : (obj n).val.obj U) (b : (obj m).val.obj U),
      ((obj (n + m)).val.map f).hom (mul U n m a b) =
        mul V n m (((obj n).val.map f).hom a) (((obj m).val.map f).hom b)) ∧
    (∀ (U : Z.left.Opensᵒᵖ) (i j k : ℤ)
      (a : (obj i).val.obj U) (b : (obj j).val.obj U) (c : (obj k).val.obj U),
      HEq (mul U (i + j) k (mul U i j a b) c)
        (mul U i (j + k) a (mul U j k b c))) ∧
    (∀ (U : Z.left.Opensᵒᵖ) (n : ℤ) (a : (obj n).val.obj U),
      HEq (mul U 0 n (one U) a) a) ∧
    (∀ (U : Z.left.Opensᵒᵖ) (n : ℤ) (a : (obj n).val.obj U),
      HEq (mul U n 0 a (one U)) a) := by sorry
  exact {
    obj := obj
    one := one
    mul := mul
    map_one := laws.1
    map_mul := laws.2.1
    mul_assoc := laws.2.2.1
    one_mul := laws.2.2.2.1
    mul_one := laws.2.2.2.2 }

/-- Nonnegative components of `pullbackAlgebra g deg` are `pullbackDegree g deg n`. -/
theorem pullbackAlgebra_obj_ofNat {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (n : ℕ) :
    (pullbackAlgebra g deg).obj (Int.ofNat n) = pullbackDegree g deg n :=
  rfl

/-- Ordinary commutativity is transported from the source algebra through the
actual pullback, restriction and degree-presentation maps. -/
theorem pullbackAlgebra_isCommutative {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) [𝒜.IsCommutative] : (pullbackAlgebra g deg).IsCommutative where
  mul_comm := sorry

/-- The actual pulled-back algebra inherits quasi-coherence from the source;
negative degrees are the zero module. -/
theorem pullbackAlgebra_isQuasicoherent {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) :
    (pullbackAlgebra g deg).IsQuasicoherent := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
