/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Yoneda
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
public import stacks_project.Chap65.Lemma_65_7_2_Pullback
public import stacks_project.Chap71.Lemma_71_11_2_Functor
public import stacks_project.Chap71.Lemma_71_2_1_Pullback
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionComposition

/-!
# Base change for relative projective functors of algebraic spaces

This leaf turns explicit pointwise comparison data into a natural isomorphism with the
categorical pullback of functors of points.
-/

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
/-- The fiber-product type underlying the base change of a relative projective functor
along a morphism from a represented scheme. -/
def baseChangeObj {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (T : (Over S)ᵒᵖ) : Type u :=
  { p : (ofOver Z).functorOfPoints.obj T × F.toFunctor.obj T //
      g.app T p.1 = F.baseMap.app T p.2 }

/-- The action on base-change points induced by a morphism of test schemes. -/
theorem baseChangeFunctorMap_property {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {T T' : (Over S)ᵒᵖ} (a : T ⟶ T')
    (p : baseChangeObj g F T) :
    g.app T' ((ofOver Z).functorOfPoints.map a p.1.1) =
      F.baseMap.app T' (F.toFunctor.map a p.1.2) :=
  sorry

/-- The raw function on base-change points induced by a morphism of test schemes. -/
def baseChangeFunctorMap {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    {T T' : (Over S)ᵒᵖ} (a : T ⟶ T') :
    baseChangeObj g F T → baseChangeObj g F T' :=
  fun p ↦
    ⟨⟨(ofOver Z).functorOfPoints.map a p.1.1, F.toFunctor.map a p.1.2⟩,
      baseChangeFunctorMap_property g F a p⟩

/-- The raw base-change point map respects identities. -/
theorem baseChangeFunctorMap_id {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (T : (Over S)ᵒᵖ) :
    baseChangeFunctorMap g F (𝟙 T) = id :=
  sorry

/-- The raw base-change point map respects composition. -/
theorem baseChangeFunctorMap_comp {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {T T' T'' : (Over S)ᵒᵖ} (a : T ⟶ T') (b : T' ⟶ T'') :
    baseChangeFunctorMap g F (a ≫ b) =
      baseChangeFunctorMap g F b ∘ baseChangeFunctorMap g F a :=
  sorry

/-- The identity law for the base-change point map as a morphism of types. -/
theorem baseChangeFunctorMap_id_hom {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (T : (Over S)ᵒᵖ) :
    TypeCat.ofHom (baseChangeFunctorMap g F (𝟙 T)) = 𝟙 (baseChangeObj g F T) :=
  sorry

/-- The composition law for the base-change point map as a morphism of types. -/
theorem baseChangeFunctorMap_comp_hom {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {T T' T'' : (Over S)ᵒᵖ} (a : T ⟶ T') (b : T' ⟶ T'') :
    TypeCat.ofHom (baseChangeFunctorMap g F (a ≫ b)) =
      TypeCat.ofHom (baseChangeFunctorMap g F a) ≫
        TypeCat.ofHom (baseChangeFunctorMap g F b) :=
  sorry

/-- The functor of points obtained by base-changing a relative projective functor. -/
def baseChangeFunctor {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj := baseChangeObj g F
  map a := TypeCat.ofHom (baseChangeFunctorMap g F a)
  map_id T := baseChangeFunctorMap_id_hom g F T
  map_comp a b := baseChangeFunctorMap_comp_hom g F a b

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
def schemeUnitOne {Z : Over S} (U : (Z.left.Opens)ᵒᵖ) :
    (SheafOfModules.unit Z.left.ringCatSheaf).val.obj U :=
  (1 : Z.left.ringCatSheaf.obj.obj U)

/-- `schemeUnitOne` is the unit of the structure sheaf of `Z.left`. -/
theorem schemeUnitOne_eq {Z : Over S} (U : (Z.left.Opens)ᵒᵖ) :
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
def pullbackAlgebraOne {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (U : (Z.left.Opens)ᵒᵖ) :
    (pullbackAlgebraObj g deg 0).val.obj U :=
  ((pullbackDegreeZeroUnit g deg).val.app U).hom
    (((schemeUnitToRestrictUnit (Z := Z)).val.app U).hom (schemeUnitOne (Z := Z) U))

/-- The restriction tensor comparison is the descent of the actual pure-tensor
pairing on opens; no equality of tensor objects or arbitrary inverse is used. -/
def restrictTensorLax {Z : Over S} (M N : (ofOver Z).Modules) :
    (Modules.restrictToScheme Z).obj M ⊗ (Modules.restrictToScheme Z).obj N ⟶
      (Modules.restrictToScheme Z).obj (M ⊗ N) :=
  Modules.RestrictToScheme.tensorLax Z M N

/-- The restriction tensor comparison is the canonical sectionwise construction. -/
theorem restrictTensorLax_eq {Z : Over S} (M N : (ofOver Z).Modules) :
    restrictTensorLax M N = Modules.RestrictToScheme.tensorLax Z M N := rfl

/-- The scheme-level multiplication of pulled-back nonnegative degree pieces, as a
morphism out of the tensor product of `pullbackDegree` modules. -/
def pullbackDegreeMulScheme {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (i j : ℕ) :
    pullbackDegree g deg i ⊗ pullbackDegree g deg j ⟶ pullbackDegree g deg (i + j) :=
  restrictTensorLax ((Modules.pullback g).obj (deg.obj i))
      ((Modules.pullback g).obj (deg.obj j)) ≫
    (Modules.restrictToScheme Z).map (pullbackDegreeMul g deg i j)

/-- `pullbackDegreeMulScheme` is `restrictTensorLax` followed by restriction of
`pullbackDegreeMul`. -/
theorem pullbackDegreeMulScheme_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (i j : ℕ) :
    pullbackDegreeMulScheme g deg i j =
      restrictTensorLax ((Modules.pullback g).obj (deg.obj i))
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
  LinearMap.mk₂ (Z.left.sheaf.obj.obj U)
    (fun x y ↦
      ((pullbackDegreeMulScheme g deg i j).val.app U).hom
        (SheafOfModules.RingedSite.tensorSection Z.left.sheaf U x y))
    sorry sorry sorry sorry

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
    GradedAlgebraSheaf.{u, u} Z.left.sheaf where
  obj := pullbackAlgebraObj g deg
  one := pullbackAlgebraOne g deg
  mul := pullbackAlgebraMul g deg
  map_one := sorry
  map_mul := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

/-- Nonnegative components of `pullbackAlgebra g deg` are `pullbackDegree g deg n`. -/
theorem pullbackAlgebra_obj_ofNat {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (n : ℕ) :
    (pullbackAlgebra g deg).obj (Int.ofNat n) = pullbackDegree g deg n :=
  rfl

/-- Ordinary commutativity is transported from the source algebra through the
actual pullback, restriction and degree-presentation maps. -/
instance pullbackAlgebra_isCommutative {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) [𝒜.IsCommutative] : (pullbackAlgebra g deg).IsCommutative where
  mul_comm := sorry

/-- The actual pulled-back algebra inherits quasi-coherence from the source;
negative degrees are the zero module. -/
theorem pullbackAlgebra_isQuasicoherent {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) :
    (pullbackAlgebra g deg).IsQuasicoherent := by
  intro n
  cases n with
  | ofNat k =>
      -- Local instance justification (proof-local temporary data): hA supplies QCoh for this displayed degree piece.
      letI := deg.isQuasicoherent hA k
      exact Modules.pullbackToScheme.instIsQuasicoherent g (deg.obj k)
  | negSucc k =>
      change (0 : Z.left.Modules).IsQuasicoherent
      sorry

/-- The categorical pullback of `g` and `F.baseMap` as functors of points. -/
abbrev functorPullback {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜) :
    (Over S)ᵒᵖ ⥤ Type u :=
  Limits.pullback
    (g : (ofOver Z).functorOfPoints ⟶ X.functorOfPoints) F.baseMap

/-- The explicit pointwise base-change type is canonically isomorphic to the value of the
categorical pullback functor. -/
def baseChangeObjIsoPullback {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (T : (Over S)ᵒᵖ) :
    baseChangeObj g F T ≅ (functorPullback g F).obj T :=
  (pullbackObjIso (g : (ofOver Z).functorOfPoints ⟶ X.functorOfPoints) F.baseMap T ≪≫
    Types.pullbackIsoPullback
      ((g : (ofOver Z).functorOfPoints ⟶ X.functorOfPoints).app T)
      (F.baseMap.app T)).symm

/-- The canonical objectwise comparison with the categorical pullback is natural in the
test scheme. -/
theorem baseChangeObjIsoPullback_naturality {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {T T' : (Over S)ᵒᵖ} (a : T ⟶ T') :
    (baseChangeFunctor g F).map a ≫ (baseChangeObjIsoPullback g F T').hom =
      (baseChangeObjIsoPullback g F T).hom ≫ (functorPullback g F).map a :=
  sorry

/-- The explicit pointwise base-change functor is canonically naturally isomorphic to the
categorical pullback functor. -/
def baseChangeFunctorIsoPullback {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) :
    baseChangeFunctor g F ≅ functorPullback g F :=
  NatIso.ofComponents (fun T ↦ baseChangeObjIsoPullback g F T)
    (fun {_ _} a ↦ baseChangeObjIsoPullback_naturality g F a)

/-- The restriction of a scheme-valued functor to schemes over `S`. -/
def schemeRestrictFunctor {Z : Over S}
    {𝒜Z : GradedAlgebraSheaf.{u, u} Z.left.sheaf}
    (F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left 𝒜Z) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := F_Z.toFunctor.obj (op T.unop.left)
  map a := F_Z.toFunctor.map (op a.unop.left)
  map_id := sorry
  map_comp := sorry

/-- `schemeRestrictFunctor` evaluates at `T` to the value of the scheme functor on `T.left`. -/
theorem schemeRestrictFunctor_obj {Z : Over S}
    {𝒜Z : GradedAlgebraSheaf.{u, u} Z.left.sheaf}
    (F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left 𝒜Z) (T : (Over S)ᵒᵖ) :
    (schemeRestrictFunctor F_Z).obj T = F_Z.toFunctor.obj (op T.unop.left) :=
  rfl

/-- Positive-degree chart functors of `underline{Proj}_Z(g^* 𝒜)` are representable. -/
instance instDegreeFunctorIsRepresentable {Z : Over S}
    {g : ofOver Z ⟶ X} {deg : DegreePieces 𝒜}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    {d : { n : ℕ // 1 ≤ n }} :
    (F_Z.degreeFunctor d).toFunctor.IsRepresentable :=
  F_Z.degreeFunctor_isRepresentable d

/-- The representing scheme of the positive-degree chart `F_Z.degreeFunctor d`. -/
def degreeChartScheme {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) : Scheme.{u} :=
  (F_Z.degreeFunctor d).toFunctor.reprX

/-- The open immersion of a positive-degree chart into `underline{Proj}_Z(g^* 𝒜)`, obtained
from `degreeToFunctor` by Yoneda of `reprW`. -/
def degreeChartImmersion {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    degreeChartScheme g deg d ⟶ F_Z.toFunctor.reprX :=
  (F_Z.toFunctor.reprW.app (op (degreeChartScheme g deg d))).inv
    ((F_Z.degreeToFunctor d).app (op (degreeChartScheme g deg d))
      (F_Z.degreeFunctor d).toFunctor.reprx)

/-- `degreeChartImmersion` is an open immersion. -/
instance degreeChartImmersion_isOpenImmersion {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    AlgebraicGeometry.IsOpenImmersion (degreeChartImmersion g deg d) :=
  sorry

/-- The structure map of a positive-degree chart to `Z.left`, obtained from
`degreeFunctor.baseMap` at the universal point. -/
def degreeChartToBase {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    degreeChartScheme g deg d ⟶ Z.left :=
  (F_Z.degreeFunctor d).baseMap.app (op (degreeChartScheme g deg d))
    (F_Z.degreeFunctor d).toFunctor.reprx

/-- The positive-degree charts form an open cover of `underline{Proj}_Z(g^* 𝒜)`. -/
def relativeProjDegreeCover {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    Scheme.OpenCover.{0} F_Z.toFunctor.reprX :=
  Scheme.Cover.mkOfCovers { n : ℕ // 1 ≤ n } (degreeChartScheme g deg)
    (degreeChartImmersion g deg) sorry (degreeChartImmersion_isOpenImmersion g deg)

/-- Compatibility of the chart structure maps on overlaps. -/
theorem degreeChartToBase_compatible {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    ∀ d e : { n : ℕ // 1 ≤ n },
      pullback.fst (degreeChartImmersion g deg d) (degreeChartImmersion g deg e) ≫
          degreeChartToBase g deg d =
        pullback.snd (degreeChartImmersion g deg d) (degreeChartImmersion g deg e) ≫
          degreeChartToBase g deg e :=
  sorry

/-- The scheme morphism `underline{Proj}_Z(g^* 𝒜) ⟶ Z.left` obtained by gluing the
positive-degree chart structure maps. -/
def relativeProjToZLeft {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    F_Z.toFunctor.reprX ⟶ Z.left :=
  Scheme.Cover.glueMorphisms (relativeProjDegreeCover g deg)
    (degreeChartToBase g deg) (degreeChartToBase_compatible g deg)

/-- The canonical structure map `underline{Proj}_Z(g^* 𝒜) ⟶ Z`, transported from
`relativeProjToZLeft` along `reprW`. -/
def relativeProjStructureMap {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    F_Z.toFunctor ⟶ yoneda.obj Z.left where
  app T := TypeCat.ofHom fun x ↦
    (F_Z.toFunctor.reprW.app T).inv x ≫ relativeProjToZLeft g deg
  naturality := sorry

/-- Positive-degree charts recover `relativeProjStructureMap`. -/
theorem relativeProjStructureMap_degree {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    F_Z.degreeToFunctor d ≫ relativeProjStructureMap g deg =
      (F_Z.degreeFunctor d).baseMap :=
  sorry

/-- The structure map is unique among maps compatible with the positive-degree charts. -/
theorem relativeProjStructureMap_unique {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (f : F_Z.toFunctor ⟶ yoneda.obj Z.left)
    (hf : ∀ d : { n : ℕ // 1 ≤ n },
      F_Z.degreeToFunctor d ≫ f = (F_Z.degreeFunctor d).baseMap) :
    f = relativeProjStructureMap g deg :=
  sorry

/-- The representing scheme of `underline{Proj}_Z(g^* 𝒜)`, as an object of `Over S`. -/
def relativeProjOver {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    Over S :=
  Over.mk (relativeProjToZLeft g deg ≫ Z.hom)

/-- The structure morphism `underline{Proj}_Z(g^* 𝒜) ⟶ Z`. -/
def relativeProjToZ {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    relativeProjOver g deg ⟶ Z :=
  Over.homMk (relativeProjToZLeft g deg) rfl

/-- The left component of `relativeProjToZ` is the glued representing structure map. -/
theorem relativeProjToZ_left {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    (relativeProjToZ g deg).left = relativeProjToZLeft g deg :=
  rfl

/-- The fiber of the scheme-level relative projective functor over a point of `Z`. -/
abbrev schemePointOver {Z : Over S}
    {𝒜Z : GradedAlgebraSheaf.{u, u} Z.left.sheaf}
    (F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left 𝒜Z)
    (baseMap : F_Z.toFunctor ⟶ yoneda.obj Z.left)
    (T : (Over S)ᵒᵖ) (t : (ofOver Z).functorOfPoints.obj T) : Type u :=
  { x : F_Z.toFunctor.obj (op T.unop.left) //
      baseMap.app (op T.unop.left) x = t.left }

/-- A compatible system of scheme-level relative Proj points on quasi-compact opens. -/
structure SchemeQcSystem {Z : Over S}
    {𝒜Z : GradedAlgebraSheaf.{u, u} Z.left.sheaf}
    (F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left 𝒜Z)
    (baseMap : F_Z.toFunctor ⟶ yoneda.obj Z.left) {T : Over S}
    (t : (ofOver Z).functorOfPoints.obj (op T)) where
  /-- The value on each quasi-compact open. -/
  restrict :
    ∀ (V : T.left.Opens) [CompactSpace V.toScheme],
      schemePointOver F_Z baseMap (op (openOver T V))
        ((ofOver Z).functorOfPoints.map (op (openOverι T V)) t)
  /-- Restriction along inclusions of quasi-compact opens. -/
  compatible :
    ∀ (V W : T.left.Opens) [CompactSpace V.toScheme] [CompactSpace W.toScheme]
      (hle : V ≤ W),
      F_Z.toFunctor.map (op (openOverιLE T hle).left) (restrict W).1 = (restrict V).1

namespace SchemeQcSystem

open AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Construct a compatible system of scheme-level points from restriction data. -/
def of {Z : Over S} {𝒜Z : GradedAlgebraSheaf.{u, u} Z.left.sheaf}
    {F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left 𝒜Z}
    {baseMap : F_Z.toFunctor ⟶ yoneda.obj Z.left} {T : Over S}
    {t : (ofOver Z).functorOfPoints.obj (op T)}
    (restrict :
      ∀ (V : T.left.Opens) [CompactSpace V.toScheme],
        schemePointOver F_Z baseMap (op (openOver T V))
          ((ofOver Z).functorOfPoints.map (op (openOverι T V)) t))
    (compatible :
      ∀ (V W : T.left.Opens) [CompactSpace V.toScheme] [CompactSpace W.toScheme]
        (hle : V ≤ W),
        F_Z.toFunctor.map (op (openOverιLE T hle).left) (restrict W).1 =
          (restrict V).1) :
    SchemeQcSystem F_Z baseMap t where
  restrict := restrict
  compatible := compatible

end SchemeQcSystem

/-- A specified factorization of every quasi-compact scheme-level point of
`underline{Proj}_Z(g^* 𝒜)` through one positive-degree chart: a degree `d`, a
point `y` of `F_Z.degreeFunctor d`, and the identities `degreeToFunctor y = x`
and `baseMap y = t.left`. This is not implied by `coveredByDegree`, which only
supplies a Zariski cover. -/
structure DegreeChartFactorization {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] where
  /-- The positive degree of the chart containing a quasi-compact scheme point. -/
  degree :
    ∀ (T : Over S) [CompactSpace T.left]
      (t : (ofOver Z).functorOfPoints.obj (op T)),
      schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t →
        { n : ℕ // 1 ≤ n }
  /-- The corresponding positive-degree chart functor point. -/
  chartPoint :
    ∀ (T : Over S) [CompactSpace T.left]
      (t : (ofOver Z).functorOfPoints.obj (op T))
      (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t),
      (F_Z.degreeFunctor (degree T t x)).toFunctor.obj (op T.left)
  /-- The chart point maps to the original scheme-level point. -/
  chartPoint_spec :
    ∀ (T : Over S) [CompactSpace T.left]
      (t : (ofOver Z).functorOfPoints.obj (op T))
      (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t),
      (F_Z.degreeToFunctor (degree T t x)).app (op T.left) (chartPoint T t x) = x.1
  /-- The chart point lies over `t.left`. -/
  chartPoint_base :
    ∀ (T : Over S) [CompactSpace T.left]
      (t : (ofOver Z).functorOfPoints.obj (op T))
      (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t),
      (F_Z.degreeFunctor (degree T t x)).baseMap.app (op T.left) (chartPoint T t x) =
        t.left

namespace DegreeChartFactorization

/-- Construct a degree-chart factorization from a choice of degree, chart point, and
the two comparison identities. -/
def of {Z : Over S} {g : ofOver Z ⟶ X} {deg : DegreePieces 𝒜}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (degree :
      ∀ (T : Over S) [CompactSpace T.left]
        (t : (ofOver Z).functorOfPoints.obj (op T)),
        schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t →
          { n : ℕ // 1 ≤ n })
    (chartPoint :
      ∀ (T : Over S) [CompactSpace T.left]
        (t : (ofOver Z).functorOfPoints.obj (op T))
        (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t),
        (F_Z.degreeFunctor (degree T t x)).toFunctor.obj (op T.left))
    (chartPoint_spec :
      ∀ (T : Over S) [CompactSpace T.left]
        (t : (ofOver Z).functorOfPoints.obj (op T))
        (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t),
        (F_Z.degreeToFunctor (degree T t x)).app (op T.left) (chartPoint T t x) = x.1)
    (chartPoint_base :
      ∀ (T : Over S) [CompactSpace T.left]
        (t : (ofOver Z).functorOfPoints.obj (op T))
        (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t),
        (F_Z.degreeFunctor (degree T t x)).baseMap.app (op T.left)
            (chartPoint T t x) =
          t.left) :
    DegreeChartFactorization g deg where
  degree := degree
  chartPoint := chartPoint
  chartPoint_spec := chartPoint_spec
  chartPoint_base := chartPoint_base

/-- The chart-point comparison identities hold simultaneously. -/
theorem conditions_spec {Z : Over S} {g : ofOver Z ⟶ X} {deg : DegreePieces 𝒜}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg) :
    (∀ (T : Over S) [CompactSpace T.left]
        (t : (ofOver Z).functorOfPoints.obj (op T))
        (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t),
      (F_Z.degreeToFunctor (hChart.degree T t x)).app (op T.left)
          (hChart.chartPoint T t x) = x.1) ∧
    (∀ (T : Over S) [CompactSpace T.left]
        (t : (ofOver Z).functorOfPoints.obj (op T))
        (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t),
      (F_Z.degreeFunctor (hChart.degree T t x)).baseMap.app (op T.left)
          (hChart.chartPoint T t x) = t.left) :=
  sorry

end DegreeChartFactorization

namespace RelativeProjBaseChangeData

open AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- The morphism `T.left ⟶ U_d` classified by a specified degree-chart point. -/
def chartPointMorphism {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    T.left ⟶ degreeChartScheme g deg (hChart.degree T t x) :=
  ((F_Z.degreeFunctor (hChart.degree T t x)).toFunctor.reprW.app
      (op T.left)).inv
    (hChart.chartPoint T t x)

/-- The positive-degree chart as a scheme over `S`. -/
def degreeChartOver {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) : Over S :=
  Over.mk (degreeChartToBase g deg d ≫ Z.hom)

/-- The degree-chart morphism as a morphism of schemes over `S`. -/
def chartPointOverHom {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    T ⟶ degreeChartOver g deg (hChart.degree T t x) :=
  Over.homMk (chartPointMorphism g deg hChart T t x) sorry

/-- The left component of `chartPointOverHom` is `chartPointMorphism`. -/
theorem chartPointOverHom_left {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    (chartPointOverHom g deg hChart T t x).left =
      chartPointMorphism g deg hChart T t x :=
  rfl

/-- Module pushforward along `schemeEtaleRingedHom` admits an inverse-image left adjoint. -/
instance instIsRightAdjoint_schemeEtaleRingedHom_modulePushforward (U : Over S) :
    ((schemeEtaleRingedHom U).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Module pushforward along `smallEtaleToOpensRingedHom` admits an inverse-image left adjoint. -/
instance instIsRightAdjoint_smallEtaleToOpensRingedHom_modulePushforward (Y : Scheme.{u}) :
    ((smallEtaleToOpensRingedHom Y).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- The inverse of `opensStructureToRingCatSheaf`, as a morphism of ring sheaves. -/
def opensSheafToRingCatSheaf (Y : Scheme.{u}) :
    (⟨Scheme.Site.structurePresheaf (Y.restrictFunctor ⋙ Over.forget Y),
        opensStructurePresheaf_isSheaf Y⟩) ⟶ Y.ringCatSheaf :=
  ⟨Functor.whiskerRight (@Scheme.restrictFunctorΓ Y).hom (forget₂ CommRingCat RingCat)⟩

/-- `opensSheafToRingCatSheaf` is whiskering of `Scheme.restrictFunctorΓ.hom`. -/
theorem opensSheafToRingCatSheaf_eq (Y : Scheme.{u}) :
    opensSheafToRingCatSheaf Y =
      ⟨Functor.whiskerRight (@Scheme.restrictFunctorΓ Y).hom (forget₂ CommRingCat RingCat)⟩ :=
  rfl

/-- Extension of a Zariski module on `U.left` to a module on `ofOver U`. -/
def extendFromScheme (U : Over S) : U.left.Modules ⥤ (ofOver U).Modules :=
  Modules.RestrictToScheme.extension U

/-- `extendFromScheme U` is restriction of scalars followed by the two inverse-image functors. -/
theorem extendFromScheme_eq (U : Over S) :
    extendFromScheme U = Modules.RestrictToScheme.extension U :=
  rfl

/-- The structure morphism of a positive-degree chart as an object of `Over S`. -/
def degreeChartToZ {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    degreeChartOver g deg d ⟶ Z :=
  Over.homMk (degreeChartToBase g deg d) rfl

/-- `degreeChartToZ` is `Over.homMk` of `degreeChartToBase`. -/
theorem degreeChartToZ_eq {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    degreeChartToZ g deg d = Over.homMk (degreeChartToBase g deg d) rfl :=
  rfl

/-- A degree-functor point has an associated scheme-level quadruple. -/
theorem exists_associatedSchemeQuadruple {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) (T : Scheme.{u})
    (y : (F_Z.degreeFunctor d).toFunctor.obj (op T)) :
    ∃ q : RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d.1 T,
      (F_Z.degreeAssociated d).associated T y q :=
  (F_Z.degreeAssociated d).exists_quadruple T y

/-- A chosen associated scheme-level quadruple of a degree-functor point. -/
noncomputable def associatedSchemeQuadruple {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) (T : Scheme.{u})
    (y : (F_Z.degreeFunctor d).toFunctor.obj (op T)) :
    RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d.1 T :=
  Classical.choose (exists_associatedSchemeQuadruple g deg d T y)

/-- The chosen quadruple is associated to the given degree-functor point. -/
theorem associatedSchemeQuadruple_spec {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) (T : Scheme.{u})
    (y : (F_Z.degreeFunctor d).toFunctor.obj (op T)) :
    (F_Z.degreeAssociated d).associated T y (associatedSchemeQuadruple g deg d T y) :=
  Classical.choose_spec (exists_associatedSchemeQuadruple g deg d T y)

/-- Equality of degree-functor points is strict equivalence of chosen associated
quadruples. -/
theorem associatedSchemeQuadruple_eq_iff {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) (T : Scheme.{u})
    (y y' : (F_Z.degreeFunctor d).toFunctor.obj (op T)) :
    y = y' ↔
      RelativeProjDegreeQuadruple.StrictlyEquivalent (pullbackAlgebra g deg) d.1
        (associatedSchemeQuadruple g deg d T y)
        (associatedSchemeQuadruple g deg d T y') :=
  (F_Z.degreeAssociated d).eq_iff T y y'
    (associatedSchemeQuadruple g deg d T y)
    (associatedSchemeQuadruple g deg d T y')
    (associatedSchemeQuadruple_spec g deg d T y)
    (associatedSchemeQuadruple_spec g deg d T y')

/-- The associated scheme quadruple of the universal point of a positive-degree chart. -/
noncomputable def universalChartQuadruple {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d.1
      (degreeChartScheme g deg d) :=
  associatedSchemeQuadruple g deg d (degreeChartScheme g deg d)
    (F_Z.degreeFunctor d).toFunctor.reprx

/-- `universalChartQuadruple` is associated to the universal degree-chart point. -/
theorem universalChartQuadruple_spec {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    (F_Z.degreeAssociated d).associated (degreeChartScheme g deg d)
      (F_Z.degreeFunctor d).toFunctor.reprx
      (universalChartQuadruple g deg d) :=
  associatedSchemeQuadruple_spec g deg d (degreeChartScheme g deg d)
    (F_Z.degreeFunctor d).toFunctor.reprx

/-- The actual pullback/extension comparison for a base-compatible scheme quadruple.
Quasi-coherence is supplied by the original graded algebra hypothesis. -/
def ofSchemePsiSourceIso {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent) {U : Over S} (d : ℕ) (t : U ⟶ Z)
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d U.left)
    (hq : q.morphism = t.left) (n : ℕ) :
    (extendFromScheme U).obj
        ((Scheme.Modules.pullback q.morphism).obj
          ((pullbackAlgebra g deg).obj (Int.ofNat (n * d)))) ≅
      (Modules.pullback (ofOverMap t ≫ g)).obj (deg.obj (n * d)) := by
  -- Local instance justification (proof-local temporary data): the supplied source law gives QCoh in degree n*d.
  letI := deg.isQuasicoherent hA (n * d)
  exact (extendFromScheme U).mapIso
      (eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
        ((pullbackAlgebra g deg).obj (Int.ofNat (n * d)))) hq)) ≪≫
    Modules.RestrictToScheme.extensionCompositePullbackIso g t (deg.obj (n * d))

/-- The pullback-form homogeneous map of a scheme quadruple, as an algebraic-space map. -/
def ofSchemePsi {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent) {U : Over S} (d : ℕ) (t : U ⟶ Z)
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d U.left)
    (hq : q.morphism = t.left) (n : ℕ) :
    (Modules.pullback (ofOverMap t ≫ g)).obj (deg.obj (n * d)) ⟶
      tensorPowerUnit ((extendFromScheme U).obj q.lineBundle) n :=
  (ofSchemePsiSourceIso g deg hA d t q hq n).inv ≫
    (extendFromScheme U).map
      (((Scheme.Modules.pullbackPushforwardAdjunction q.morphism).homEquiv
          ((pullbackAlgebra g deg).obj (Int.ofNat (n * d)))
          (RingedSpace.TensorPower.sheaf q.lineBundle n)).symm (q.psi n)) ≫
    (Modules.RestrictToScheme.extensionTensorPowerIso U q.lineBundle n).hom

/-- Convert a scheme-level fixed-degree quadruple to an algebraic-space quadruple. -/
def ofSchemeQuadruple {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent) {U : Over S} (d : ℕ) (hd : 1 ≤ d) (t : U ⟶ Z)
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d U.left)
    (hq : q.morphism = t.left) :
    Quadruple 𝒜 deg U :=
  Quadruple.of d hd (ofOverMap t ≫ g) ((extendFromScheme U).obj q.lineBundle) sorry
    (ofSchemePsi g deg hA d t q hq) sorry sorry
    (ofSchemePsi g deg hA d t q hq 1) sorry sorry

/-- The line bundle of `ofSchemeQuadruple` is the extension of the scheme-level line bundle. -/
theorem ofSchemeQuadruple_lineBundle {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) {U : Over S} (d : ℕ) (hd : 1 ≤ d)
    (t : U ⟶ Z)
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d U.left)
    (hq : q.morphism = t.left) :
    (ofSchemeQuadruple g deg hA d hd t q hq).lineBundle =
      (extendFromScheme U).obj q.lineBundle :=
  rfl

/-- The morphism of a positive-degree chart into `underline{Proj}_Z(g^* 𝒜)`. -/
def degreeChartToRelativeProj {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    degreeChartOver g deg d ⟶ relativeProjOver g deg :=
  Over.homMk (degreeChartImmersion g deg d) sorry

/-- The algebraic-space quadruple of the universal point of a positive-degree chart. -/
def universalSpaceQuadruple {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    Quadruple 𝒜 deg (degreeChartOver g deg d) :=
  ofSchemeQuadruple g deg hA d.1 d.2 (degreeChartToZ g deg d)
    (universalChartQuadruple g deg d) sorry

/-- The structure morphism of `universalSpaceQuadruple` is the chart map followed by `g`. -/
theorem universalSpaceQuadruple_morphism {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    (universalSpaceQuadruple g deg hA d).morphism =
      ofOverMap (degreeChartToZ g deg d) ≫ g :=
  rfl

/-- Pushalong of the universal chart quadruple along `g`, sending
`(d, f, L, ψ)` to `(d, g ∘ f, L, ψ)`. -/
def chartPushalong {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    Quadruple 𝒜 deg (degreeChartOver g deg d) :=
  Quadruple.pushalong (ofOverMap (degreeChartToZ g deg d)) g
    (universalSpaceQuadruple g deg hA d)
    (universalSpaceQuadruple_morphism g deg hA d)

/-- The line bundle of `chartPushalong` is the line bundle of the universal chart
quadruple. -/
theorem chartPushalong_lineBundle {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    (chartPushalong g deg hA d).lineBundle =
      (universalSpaceQuadruple g deg hA d).lineBundle :=
  rfl

/-- The `F`-point of a quasi-compact open of a positive-degree chart, obtained by
classifying the pullback of `chartPushalong`. -/
def chartOpenPointOf {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) (V : (degreeChartOver g deg d).left.Opens)
    [CompactSpace V.toScheme] :
    F.toFunctor.obj (op (openOver (degreeChartOver g deg d) V)) :=
  hF.pointOf (openOver (degreeChartOver g deg d) V)
    (Quadruple.pullback (openOverι (degreeChartOver g deg d) V)
      (chartPushalong g deg F.algebra_isQuasicoherent d))

/-- The `F`-point of a positive-degree chart, obtained by the quasi-compact open limit
of the chartwise classifying maps. -/
def chartPointOf {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    F.toFunctor.obj (op (degreeChartOver g deg d)) :=
  (hF.qcLimit (degreeChartOver g deg d)).symm
    (ProjFunctor.QcCompatibleSystem.of
      (fun V ↦ chartOpenPointOf g F hF d V) sorry)

/-- The test object obtained by pulling a degree chart back along a morphism into
`underline{Proj}_Z`. Each such piece factors through one chart by construction. -/
def pulledDegreeChartOver {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    {T : Over S} (φ : T.left ⟶ F_Z.toFunctor.reprX) (d : { n : ℕ // 1 ≤ n }) :
    Over S :=
  Over.mk (((relativeProjDegreeCover g deg).pullback₁ φ).f d ≫ T.hom)

/-- The morphism from a pulled degree-chart piece to the corresponding chart. -/
def pulledDegreeChartHom {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    {T : Over S} (φ : T.left ⟶ F_Z.toFunctor.reprX)
    (hφ : φ ≫ (relativeProjOver g deg).hom = T.hom) (d : { n : ℕ // 1 ≤ n }) :
    pulledDegreeChartOver g deg φ d ⟶ degreeChartOver g deg d :=
  Over.homMk (pullback.snd φ (degreeChartImmersion g deg d)) sorry

/-- The `F`-point of a pulled degree-chart piece, obtained by transporting
`chartPointOf` along the chart morphism. -/
def pulledDegreeChartPointOf {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    {T : Over S} (φ : T.left ⟶ F_Z.toFunctor.reprX)
    (hφ : φ ≫ (relativeProjOver g deg).hom = T.hom) (d : { n : ℕ // 1 ≤ n }) :
    F.toFunctor.obj (op (pulledDegreeChartOver g deg φ d)) :=
  F.toFunctor.map (op (pulledDegreeChartHom g deg φ hφ d))
    (chartPointOf g F hF d)

/-- The morphism into `underline{Proj}_Z(g^* 𝒜)` classified by a map into the
representing scheme. -/
def overHomOfReprMap {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    {T : Over S} (φ : T.left ⟶ F_Z.toFunctor.reprX)
    (hφ : φ ≫ (relativeProjOver g deg).hom = T.hom) :
    T ⟶ relativeProjOver g deg :=
  Over.homMk φ hφ

/-- The left component of `overHomOfReprMap` is the given representing-scheme map. -/
theorem overHomOfReprMap_left {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    {T : Over S} (φ : T.left ⟶ F_Z.toFunctor.reprX)
    (hφ : φ ≫ (relativeProjOver g deg).hom = T.hom) :
    (overHomOfReprMap g deg φ hφ).left = φ :=
  rfl

/-- The positive common degree of the finite pullback cover of a quasi-compact open.
The empty finite cover contributes the product1. -/
noncomputable def chartIndexOfOpens {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (V : (relativeProjOver g deg).left.Opens) [CompactSpace V.toScheme] :
    { n : ℕ // 1 ≤ n } :=
  AlgebraicGeometry.RelativeProjFunctor.commonDegree (F := F_Z) V.ι

/-- The morphism from a quasi-compact open of `underline{Proj}_Z` to the positive-degree
chart containing the image of its full finite cover. -/
def openOverToDegreeChart {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (V : (relativeProjOver g deg).left.Opens) [CompactSpace V.toScheme] :
    openOver (relativeProjOver g deg) V ⟶
      degreeChartOver g deg (chartIndexOfOpens g deg V) :=
  Over.homMk
    (@IsOpenImmersion.lift
      (degreeChartScheme g deg (chartIndexOfOpens g deg V))
      (openOver (relativeProjOver g deg) V).left
      F_Z.toFunctor.reprX
      (degreeChartImmersion g deg (chartIndexOfOpens g deg V))
      (openOverι (relativeProjOver g deg) V).left
      (degreeChartImmersion_isOpenImmersion g deg (chartIndexOfOpens g deg V))
      (AlgebraicGeometry.RelativeProjFunctor.range_subset_commonDegree
        (F := F_Z) V.ι))
    sorry

/-- The `F`-point of a quasi-compact open of `underline{Proj}_Z`, obtained by classifying
the pullback of the chartwise pushalong of the universal chart quadruple. -/
def fPointOnOpenOfRelativeProj {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (V : (relativeProjOver g deg).left.Opens) [CompactSpace V.toScheme] :
    F.toFunctor.obj (op (openOver (relativeProjOver g deg) V)) :=
  hF.pointOf (openOver (relativeProjOver g deg) V)
    (Quadruple.pullback (openOverToDegreeChart g deg V)
      (chartPushalong g deg F.algebra_isQuasicoherent (chartIndexOfOpens g deg V)))

/-- The `F`-point of `underline{Proj}_Z(g^* 𝒜)`, obtained by the quasi-compact open
limit of the chartwise classifying maps. -/
def relativeProjFPoint {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    F.toFunctor.obj (op (relativeProjOver g deg)) :=
  (hF.qcLimit (relativeProjOver g deg)).symm
    (ProjFunctor.QcCompatibleSystem.of
      (fun V ↦ fPointOnOpenOfRelativeProj g F hF V) sorry)

/-- The `F`-point of a test object classified by a map into `underline{Proj}_Z`, obtained
by restricting `relativeProjFPoint` along the representing-scheme map. -/
def fPointOfReprMap {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    {T : Over S} (φ : T.left ⟶ F_Z.toFunctor.reprX)
    (hφ : φ ≫ (relativeProjOver g deg).hom = T.hom) :
    F.toFunctor.obj (op T) :=
  F.toFunctor.map (op (overHomOfReprMap g deg φ hφ))
    (relativeProjFPoint g F hF)

/-- The associated scheme-level quadruple of a specified degree-chart point. -/
noncomputable def associatedChartQuadruple {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    RelativeProjDegreeQuadruple (pullbackAlgebra g deg)
      (hChart.degree T t x).1 T.left :=
  associatedSchemeQuadruple g deg (hChart.degree T t x) T.left
    (hChart.chartPoint T t x)

/-- `associatedChartQuadruple` is associated to the specified chart point. -/
theorem associatedChartQuadruple_spec {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    (F_Z.degreeAssociated (hChart.degree T t x)).associated T.left (hChart.chartPoint T t x)
      (associatedChartQuadruple g deg hChart T t x) :=
  sorry

/-- The degree-chart quadruple of a quasi-compact scheme-level point, obtained by
transporting the associated scheme quadruple of the specified chart point `y`
along `chartPointOverHom` and viewing the result over `X` via `t ≫ g`. -/
def degreeChartQuadruple {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    Quadruple 𝒜 deg T :=
  let d := hChart.degree T t x
  ofSchemeQuadruple g deg hA d.1 d.2 t
    (associatedChartQuadruple g deg hChart T t x) sorry

/-- The structure morphism of `degreeChartQuadruple` is `t ≫ g`. -/
theorem degreeChartQuadruple_morphism {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    (degreeChartQuadruple g deg hA hChart T t x).morphism = ofOverMap t ≫ g :=
  rfl

/-- `degreeChartQuadruple` preserves the specified chart Veronese degree. -/
theorem degreeChartQuadruple_degree {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    (degreeChartQuadruple g deg hA hChart T t x).degree =
      (hChart.degree T t x).1 :=
  rfl

/-- The line bundle of `degreeChartQuadruple` is the extension of the associated
scheme-level line bundle of the specified chart point. -/
theorem degreeChartQuadruple_lineBundle {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    (degreeChartQuadruple g deg hA hChart T t x).lineBundle =
      (extendFromScheme T).obj
        (associatedChartQuadruple g deg hChart T t x).lineBundle :=
  rfl

/-- `degreeChartQuadruple` is equivalent to the pullback of the universal chart
quadruple along `chartPointOverHom`. -/
theorem degreeChartQuadruple_eq_pullback {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (hChart : DegreeChartFactorization g deg)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    Quadruple.Equivalent
      (degreeChartQuadruple g deg hA hChart T t x)
      (Quadruple.pullback (chartPointOverHom g deg hChart T t x)
        (universalSpaceQuadruple g deg hA (hChart.degree T t x))) :=
  sorry

/-- The actual source map uses the restriction/pullback mate and composition
of pullbacks, with the quadruple's base morphism explicitly identified. -/
def toSchemePsiSource {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    {T : Over S} (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) (n : ℕ) :
    (Scheme.Modules.pullback t.left).obj
        ((pullbackAlgebra g deg).obj (Int.ofNat (n * q.degree))) ⟶
      (Modules.restrictToScheme T).obj
        ((Modules.pullback q.morphism).obj (deg.obj (n * q.degree))) :=
  Modules.RestrictToScheme.pullbackComparison t
      ((Modules.pullback g).obj (deg.obj (n * q.degree))) ≫
    (Modules.restrictToScheme T).map
      ((Modules.pullbackCompIso (ofOverMap t) g).hom.app (deg.obj (n * q.degree)) ≫
        eqToHom (congrArg (fun f ↦ (Modules.pullback f).obj
          (deg.obj (n * q.degree))) hq.symm))

/-- The restriction tensor comparison for the quadruple's invertible module. -/
def toSchemeTensorIso {deg : DegreePieces 𝒜} {T : Over S} (q : Quadruple 𝒜 deg T) (n : ℕ) :
    RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme T).obj q.lineBundle) n ≅
      (Modules.restrictToScheme T).obj (tensorPowerUnit q.lineBundle n) := by
  -- Local instance justification (proof-local temporary data): this quadruple's invertibility gives its line module QCoh.
  letI := Modules.RestrictToScheme.invertible_isQuasicoherent T q.lineBundle
    q.lineBundle_invertible
  exact Modules.RestrictToScheme.tensorPowerIso T q.lineBundle n

/-- The scheme-level homogeneous map associated to an algebraic-space quadruple. -/
def toSchemePsi {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    {T : Over S} (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) (n : ℕ) :
    (pullbackAlgebra g deg).obj (Int.ofNat (n * q.degree)) ⟶
      (Scheme.Modules.pushforward t.left).obj
        (RingedSpace.TensorPower.sheaf
          ((Modules.restrictToScheme T).obj q.lineBundle) n) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction t.left).homEquiv
      ((pullbackAlgebra g deg).obj (Int.ofNat (n * q.degree)))
      (RingedSpace.TensorPower.sheaf
        ((Modules.restrictToScheme T).obj q.lineBundle) n)).toFun
    (toSchemePsiSource (T := T) g deg t q hq n ≫
      (Modules.restrictToScheme T).map (q.psi n) ≫
        (toSchemeTensorIso (T := T) q n).inv)

/-- The actual adjoint of the degree-one homogeneous map. -/
def toSchemeDegreeOneMap {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    {T : Over S} (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) :
    (Scheme.Modules.pullback t.left).obj
        ((pullbackAlgebra g deg).obj (Int.ofNat (1 * q.degree))) ⟶
      RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme T).obj q.lineBundle) 1 :=
  ((Scheme.Modules.pullbackPushforwardAdjunction t.left).homEquiv
      ((pullbackAlgebra g deg).obj (Int.ofNat (1 * q.degree)))
      (RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme T).obj q.lineBundle) 1)).symm
    (toSchemePsi (T := T) g deg t q hq 1)

/-- Restriction preserves the quadruple's invertible module. -/
theorem toSchemeLineBundle_invertible {deg : DegreePieces 𝒜} {T : Over S}
    (q : Quadruple 𝒜 deg T) :
    Scheme.Modules.Invertible ((Modules.restrictToScheme T).obj q.lineBundle) := sorry

/-- The transported map sends the unit to the actual tensor-power unit. -/
theorem toSchemePsi_map_one {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    {T : Over S} (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) (V : Z.left.Opens) :
    (((toSchemePsi (T := T) g deg t q hq 0).val.app (op V)).hom
      (Eq.mp (RelativeProjDegreeQuadruple.sourceZeroSectionEq
        (pullbackAlgebra g deg) V q.degree) ((pullbackAlgebra g deg).one (op V)))) =
      TensorPower.oneSection T.left.sheaf ((Modules.restrictToScheme T).obj q.lineBundle)
        (op (t.left ⁻¹ᵁ V)) := sorry

/-- Tensor compatibility identifies the transported graded multiplications. -/
theorem toSchemePsi_map_mul {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    {T : Over S} (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) (V : Z.left.Opens) (i j : ℕ)
    (x : ((pullbackAlgebra g deg).obj (Int.ofNat (i * q.degree))).val.obj (op V))
    (y : ((pullbackAlgebra g deg).obj (Int.ofNat (j * q.degree))).val.obj (op V)) :
    (((toSchemePsi (T := T) g deg t q hq (i + j)).val.app (op V)).hom
      (Eq.mp (RelativeProjDegreeQuadruple.sourceMulSectionEq
        (pullbackAlgebra g deg) V i j q.degree)
        ((pullbackAlgebra g deg).mul (op V)
          (Int.ofNat (i * q.degree)) (Int.ofNat (j * q.degree)) x y))) =
      TensorPower.mulSection T.left.sheaf ((Modules.restrictToScheme T).obj q.lineBundle)
        (op (t.left ⁻¹ᵁ V)) i j
        (((toSchemePsi (T := T) g deg t q hq i).val.app (op V)).hom x)
        (((toSchemePsi (T := T) g deg t q hq j).val.app (op V)).hom y) := sorry

/-- The specified degree-one map is the adjoint of degree one. -/
theorem toSchemeDegreeOneMap_spec {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    {T : Over S} (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) :
    ((Scheme.Modules.pullbackPushforwardAdjunction t.left).homEquiv
      ((pullbackAlgebra g deg).obj (Int.ofNat (1 * q.degree)))
      (RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme T).obj q.lineBundle) 1))
        (toSchemeDegreeOneMap (T := T) g deg t q hq) = toSchemePsi (T := T) g deg t q hq 1 :=
  Equiv.apply_symm_apply _ _

/-- The epi transports through QCoh comparison; the algebra hypothesis is the source's. -/
theorem toSchemeDegreeOneMap_epi {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent) {T : Over S} (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) : Epi (toSchemeDegreeOneMap (T := T) g deg t q hq) := sorry

/-- Convert an algebraic-space quadruple over `t ≫ g` to a scheme-level quadruple on
`T.left`. -/
def toSchemeQuadruple {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent)
    {T : Over S} (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) :
    RelativeProjDegreeQuadruple (pullbackAlgebra g deg) q.degree T.left where
  morphism := t.left
  lineBundle := (Modules.restrictToScheme T).obj q.lineBundle
  lineBundle_invertible := toSchemeLineBundle_invertible (T := T) q
  psi := toSchemePsi (T := T) g deg t q hq
  psi_map_one := toSchemePsi_map_one (T := T) g deg t q hq
  psi_map_mul := toSchemePsi_map_mul (T := T) g deg t q hq
  degreeOneMap := toSchemeDegreeOneMap (T := T) g deg t q hq
  degreeOneMap_spec := toSchemeDegreeOneMap_spec (T := T) g deg t q hq
  degreeOne_surjective := toSchemeDegreeOneMap_epi (T := T) g deg hA t q hq

/-- The structure morphism of `toSchemeQuadruple` is `t.left`. -/
theorem toSchemeQuadruple_morphism {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) {T : Over S}
    (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) :
    (toSchemeQuadruple (T := T) g deg hA t q hq).morphism = t.left :=
  rfl

/-- A scheme-level quadruple has an associated degree-functor point. -/
theorem exists_schemePointOfQuadruple {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (T : Over S) (t : T ⟶ Z)
    (q : Quadruple 𝒜 deg T) (hq : q.morphism = ofOverMap t ≫ g) :
    ∃ y : (F_Z.degreeFunctor ⟨q.degree, q.positive⟩).toFunctor.obj (op T.left),
      (F_Z.degreeAssociated ⟨q.degree, q.positive⟩).associated T.left y
        (toSchemeQuadruple (T := T) g deg hA t q hq) :=
  (F_Z.degreeAssociated ⟨q.degree, q.positive⟩).exists_point T.left
    (toSchemeQuadruple (T := T) g deg hA t q hq)

/-- The scheme-level point of relative Proj associated to a quadruple over `t`, obtained
by inverting the degree-functor association. -/
noncomputable def schemePointOfQuadruple {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (T : Over S) [CompactSpace T.left]
    (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) :
    schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t :=
  let d : { n : ℕ // 1 ≤ n } := ⟨q.degree, q.positive⟩
  let y := Classical.choose (exists_schemePointOfQuadruple g deg hA T t q hq)
  ⟨(F_Z.degreeToFunctor d).app (op T.left) y, sorry⟩

/-- The chosen degree-functor point of `schemePointOfQuadruple` is associated to
`toSchemeQuadruple`. -/
theorem schemePointOfQuadruple_associated {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (T : Over S) [CompactSpace T.left]
    (t : T ⟶ Z) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) :
    (F_Z.degreeAssociated ⟨q.degree, q.positive⟩).associated T.left
      (Classical.choose (exists_schemePointOfQuadruple g deg hA T t q hq))
      (toSchemeQuadruple (T := T) g deg hA t q hq) :=
  Classical.choose_spec (exists_schemePointOfQuadruple g deg hA T t q hq)

end RelativeProjBaseChangeData

/-- Canonical comparison data identifying scheme-level relative Proj of `g^* 𝒜` with the
base change of `F`, via chartwise pushalong of universal chart quadruples
`(d, f, L, ψ) ↦ (d, g ∘ f, L, ψ)` along the positive-degree cover, glued by the
quasi-compact open limit. -/
structure RelativeProjBaseChangeData {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (deg : DegreePieces 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] where
  /-- A general scheme-level point is a compatible system of quasi-compact points. -/
  schemeQcLimit :
    ∀ (T : Over S) (t : (ofOver Z).functorOfPoints.obj (op T)),
      schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t ≃
        SchemeQcSystem F_Z (relativeProjStructureMap g deg) t
  /-- The compatible system of a scheme-level point is restriction along `openOverι`. -/
  schemeQcLimit_restrict :
    ∀ (T : Over S) (t : (ofOver Z).functorOfPoints.obj (op T))
      (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t)
      (V : T.left.Opens) [CompactSpace V.toScheme],
      ((schemeQcLimit T t x).restrict V).1 =
        F_Z.toFunctor.map (op (openOverι T V).left) x.1


namespace RelativeProjBaseChangeData

/-- The degreewise classification is owned by the coherent relative Proj presentation. -/
def associatedToQuadruples {Z : Over S} {g : ofOver Z ⟶ X}
    {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (_data : RelativeProjBaseChangeData g F deg hF) :
    ∀ d : {n : ℕ // 1 ≤ n}, (F_Z.degreeFunctor d).IsAssociatedToQuadruples :=
  F_Z.degreeAssociated

/-- The inverse on quasi-compact points is the actual classifying construction,
not an unconstrained function stored in comparison data. -/
def schemePointOf {Z : Over S} {g : ofOver Z ⟶ X}
    {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (_data : RelativeProjBaseChangeData g F deg hF)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T)) (q : Quadruple 𝒜 deg T)
    (hq : q.morphism = ofOverMap t ≫ g) :
    schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t :=
  schemePointOfQuadruple g deg F.algebra_isQuasicoherent T t q hq

/-- Canonical comparison data from chartwise pushalong of universal chart quadruples
`(d, f, L, ψ) ↦ (d, g ∘ f, L, ψ)` along the positive-degree cover. -/
noncomputable def ofPushalong {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    RelativeProjBaseChangeData g F deg hF where
  schemeQcLimit := fun T t ↦
    Equiv.ofBijective
      (fun x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t ↦
        SchemeQcSystem.of
          (fun V _ ↦
            ⟨F_Z.toFunctor.map (op (openOverι T V).left) x.1, sorry⟩)
          sorry)
      sorry
  schemeQcLimit_restrict := sorry

/-- `ofPushalong` uses the coherent owner's degreewise association. -/
theorem ofPushalong_associatedToQuadruples {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    (ofPushalong g F hF).associatedToQuadruples = F_Z.degreeAssociated :=
  rfl

/-- The chartwise pushalong, inverse on quasi-compact tests, and quasi-compact limit
conditions hold simultaneously. -/
theorem conditions_spec {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF) :
    (∀ d : { n : ℕ // 1 ≤ n },
      (chartPushalong g deg F.algebra_isQuasicoherent d).morphism =
        ofOverMap (degreeChartToZ g deg d) ≫ g) ∧
    (∀ d : { n : ℕ // 1 ≤ n },
      (chartPushalong g deg F.algebra_isQuasicoherent d).degree = d.1) ∧
    (∀ d : { n : ℕ // 1 ≤ n },
      (chartPushalong g deg F.algebra_isQuasicoherent d).lineBundle =
        (universalSpaceQuadruple g deg F.algebra_isQuasicoherent d).lineBundle) ∧
    (∀ (T : Over S) [CompactSpace T.left]
        (t : (ofOver Z).functorOfPoints.obj (op T)) (q : Quadruple 𝒜 deg T)
        (hq : q.morphism = ofOverMap t ≫ g),
      (data.schemePointOf T t q hq).1 =
        (schemePointOfQuadruple g deg F.algebra_isQuasicoherent T t q hq).1) ∧
    (∀ (T : Over S) (t : (ofOver Z).functorOfPoints.obj (op T))
        (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t)
        (V : T.left.Opens) [CompactSpace V.toScheme],
      ((data.schemeQcLimit T t x).restrict V).1 =
        F_Z.toFunctor.map (op (openOverι T V).left) x.1) :=
  sorry

/-- The morphism of a test object into `underline{Proj}_Z` classified by a scheme-level
point. -/
def schemePointMorphism {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    {T : Over S}
    (x : F_Z.toFunctor.obj (op T.left)) :
    T.left ⟶ F_Z.toFunctor.reprX :=
  (F_Z.toFunctor.reprW.app (op T.left)).inv x

/-- The forward `F`-point of a scheme-level point, obtained by restricting the
chartwise `F`-point of `underline{Proj}_Z` along the representing-scheme map. -/
noncomputable def pointOfPulledDegreeCover {Z : Over S} {g : ofOver Z ⟶ X}
    {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    {T : Over S} (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    F.toFunctor.obj (op T) :=
  fPointOfReprMap g F hF (schemePointMorphism g deg x.1) sorry

/-- The fiber equivalence on a quasi-compact test object, sending a scheme-level point
to the class of the chartwise pushalong after pulling back the degree cover. -/
noncomputable def pointEquivQc {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T)) :
    schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t ≃
      F.pointOver (op T) (g.app (op T) t) where
  toFun x :=
    ⟨pointOfPulledDegreeCover (hF := hF) t x, sorry⟩
  invFun y :=
    data.schemePointOf T t (hF.quadrupleOf T y.1) sorry
  left_inv := sorry
  right_inv := sorry

/-- The image of a scheme-level point is associated to a chartwise pushalong of a
quadruple of `g^* 𝒜`. -/
theorem pointEquivQc_spec {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF)
    (T : Over S) [CompactSpace T.left]
    (t : (ofOver Z).functorOfPoints.obj (op T))
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t) :
    ∃ d : { n : ℕ // 1 ≤ n },
      ∃ q : Quadruple 𝒜 deg T,
        q.degree = d.1 ∧
          q.morphism = ofOverMap t ≫ g ∧
            hF.associated T (data.pointEquivQc T t x).1 q :=
  sorry

/-- The fiber equivalence on a general test object. Quasi-compact opens are compared
after pulling back the positive-degree cover so each piece factors through one chart;
the resulting compatible system is glued by `hF.qcLimit`. -/
noncomputable def pointEquiv {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF)
    (T : (Over S)ᵒᵖ) (t : (ofOver Z).functorOfPoints.obj T) :
    schemePointOver F_Z (relativeProjStructureMap g deg) T t ≃ F.pointOver T (g.app T t) where
  toFun x :=
    ⟨pointOfPulledDegreeCover (hF := hF) t x, sorry⟩
  invFun y :=
    (data.schemeQcLimit T.unop t).symm
      (SchemeQcSystem.of
        (fun V _ ↦
          let tV := (ofOver Z).functorOfPoints.map (op (openOverι T.unop V)) t
          let yV : F.pointOver (op (openOver T.unop V))
              (g.app (op (openOver T.unop V)) tV) :=
            ⟨F.toFunctor.map (op (openOverι T.unop V)) y.1, sorry⟩
          data.schemePointOf (openOver T.unop V) tV
            (hF.quadrupleOf (openOver T.unop V) yV.1) sorry)
        sorry)
  left_inv := sorry
  right_inv := sorry

/-- The constructed fiber equivalences are natural in the test scheme. -/
theorem pointEquiv_natural {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF)
    {T T' : (Over S)ᵒᵖ} (a : T ⟶ T')
    (t : (ofOver Z).functorOfPoints.obj T)
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) T t) :
    (data.pointEquiv T' ((ofOver Z).functorOfPoints.map a t)
        ⟨F_Z.toFunctor.map (op a.unop.left) x.1, sorry⟩).1 =
      F.toFunctor.map a (data.pointEquiv T t x).1 :=
  sorry

/-- The identity morphism of `relativeProjOver` as a point of `Z`. -/
def structurePoint {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    (ofOver Z).functorOfPoints.obj (op (relativeProjOver g deg)) :=
  relativeProjToZ g deg

/-- Forward raw point map from a morphism into `underline{Proj}_Z(g^* 𝒜)` to a
base-change pair. -/
def homApp {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF)
    (T : (Over S)ᵒᵖ)
    (f : T.unop ⟶ relativeProjOver g deg) :
    baseChangeObj g F T :=
  let t : (ofOver Z).functorOfPoints.obj T := f ≫ relativeProjToZ g deg
  let y := (F_Z.toFunctor.reprW.app (op T.unop.left)).hom f.left
  let z := data.pointEquiv T t ⟨y, sorry⟩
  ⟨⟨t, z.1⟩, z.2.symm⟩

/-- Inverse raw point map from a base-change pair to a morphism into
`underline{Proj}_Z(g^* 𝒜)`. -/
def invApp {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF)
    (T : (Over S)ᵒᵖ) (p : baseChangeObj g F T) :
    T.unop ⟶ relativeProjOver g deg :=
  let z : F.pointOver T (g.app T p.1.1) := ⟨p.1.2, p.2.symm⟩
  let y := (data.pointEquiv T p.1.1).symm z
  Over.homMk ((F_Z.toFunctor.reprW.app (op T.unop.left)).inv y.1) sorry

/-- The forward maps `homApp` are natural in the test scheme. -/
theorem homApp_natural {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF)
    {T T' : (Over S)ᵒᵖ} (a : T ⟶ T') :
    (yoneda.obj (relativeProjOver g deg)).map a ≫
        TypeCat.ofHom (data.homApp T') =
      TypeCat.ofHom (data.homApp T) ≫ (baseChangeFunctor g F).map a :=
  sorry

/-- The inverse maps `invApp` are natural in the test scheme. -/
theorem invApp_natural {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF)
    {T T' : (Over S)ᵒᵖ} (a : T ⟶ T') :
    (baseChangeFunctor g F).map a ≫ TypeCat.ofHom (data.invApp T') =
      TypeCat.ofHom (data.invApp T) ≫
        (yoneda.obj (relativeProjOver g deg)).map a :=
  sorry

/-- The forward natural transformation from Yoneda of relative Proj to the explicit
base-change functor. -/
def toBaseChangeIsoHom {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF) :
    yoneda.obj (relativeProjOver g deg) ⟶ baseChangeFunctor g F where
  app T := TypeCat.ofHom (data.homApp T)
  naturality := fun {_ _} a ↦ data.homApp_natural a

/-- The inverse natural transformation from the explicit base-change functor to Yoneda
of relative Proj. -/
def toBaseChangeIsoInv {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF) :
    baseChangeFunctor g F ⟶ yoneda.obj (relativeProjOver g deg) where
  app T := TypeCat.ofHom (data.invApp T)
  naturality := fun {_ _} a ↦ data.invApp_natural a

/-- The forward and inverse transformations compose to the identity on Yoneda of
relative Proj. -/
theorem toBaseChangeIso_hom_inv_id {Z : Over S} {g : ofOver Z ⟶ X}
    {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF) :
    data.toBaseChangeIsoHom ≫ data.toBaseChangeIsoInv =
      𝟙 (yoneda.obj (relativeProjOver g deg)) :=
  sorry

/-- The inverse and forward transformations compose to the identity on the
base-change functor. -/
theorem toBaseChangeIso_inv_hom_id {Z : Over S} {g : ofOver Z ⟶ X}
    {F : ProjFunctor X 𝒜} {deg : DegreePieces 𝒜}
    {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF) :
    data.toBaseChangeIsoInv ≫ data.toBaseChangeIsoHom =
      𝟙 (baseChangeFunctor g F) :=
  sorry

/-- The natural isomorphism between Yoneda of `underline{Proj}_Z(g^* 𝒜)` and the
explicit base-change functor. -/
def toBaseChangeIso {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF) :
    yoneda.obj (relativeProjOver g deg) ≅ baseChangeFunctor g F where
  hom := data.toBaseChangeIsoHom
  inv := data.toBaseChangeIsoInv
  hom_inv_id := data.toBaseChangeIso_hom_inv_id
  inv_hom_id := data.toBaseChangeIso_inv_hom_id

/-- The canonical isomorphism `yoneda.obj underline{Proj}_Z(g^* 𝒜) ≅ Z ×_X F` of
functors of points. -/
def toPullbackIso' {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF) :
    yoneda.obj (relativeProjOver g deg) ≅ functorPullback g F :=
  data.toBaseChangeIso ≪≫ baseChangeFunctorIsoPullback g F

/-- The Over-morphism `Z' ⟶ Z` recovered from a morphism of represented algebraic
spaces. -/
def overHomOf {Z Z' : Over S} (h : ofOver Z' ⟶ ofOver Z) : Z' ⟶ Z :=
  Yoneda.fullyFaithful.preimage h

/-- `overHomOf h` is the Yoneda preimage of `h`. -/
theorem overHomOf_eq {Z Z' : Over S} (h : ofOver Z' ⟶ ofOver Z) :
    overHomOf h = Yoneda.fullyFaithful.preimage h :=
  rfl

/-- Pullback of `g^* 𝒜` along `h`, through the actual restriction/composition maps. -/
def pushSchemeAlgebraPullIso {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent) (n : ℕ) :
    (Scheme.Modules.pullback (overHomOf (Z := Z) (Z' := Z') h).left).obj
        ((pullbackAlgebra g deg).obj (Int.ofNat n)) ≅
      (pullbackAlgebra (h ≫ g) deg).obj (Int.ofNat n) := by
  -- Local instance justification (proof-local temporary data): hA gives QCoh for this input degree before base change.
  letI := deg.isQuasicoherent hA n
  exact Modules.RestrictToScheme.compositePullbackIso g (overHomOf (Z := Z) (Z' := Z') h) (deg.obj n) ≪≫
    (Modules.restrictToScheme Z').mapIso
      (eqToIso (congrArg (fun f ↦ (Modules.pullback (f ≫ g)).obj (deg.obj n))
        (Yoneda.fullyFaithful.map_preimage h)))

/-- Homogeneous maps of a scheme quadruple after composing the structure morphism
with `overHomOf (Z := Z) (Z' := Z') h`. -/
def pushSchemePsi {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent) {d : ℕ} {T : Scheme.{u}}
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra (h ≫ g) deg) d T)
    (n : ℕ) :
    (pullbackAlgebra g deg).obj (Int.ofNat (n * d)) ⟶
      (Scheme.Modules.pushforward (q.morphism ≫ (overHomOf (Z := Z) (Z' := Z') h).left)).obj
        (RingedSpace.TensorPower.sheaf q.lineBundle n) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (overHomOf (Z := Z) (Z' := Z') h).left).unit.app
      ((pullbackAlgebra g deg).obj (Int.ofNat (n * d))) ≫
    (Scheme.Modules.pushforward (overHomOf (Z := Z) (Z' := Z') h).left).map
      ((pushSchemeAlgebraPullIso g h deg hA (n * d)).hom ≫ q.psi n) ≫
    (Scheme.Modules.pushforwardComp q.morphism (overHomOf (Z := Z) (Z' := Z') h).left).hom.app
      (RingedSpace.TensorPower.sheaf q.lineBundle n)

/-- The degree-one component of `pushSchemePsi`, as the adjoint of the degree-one
homogeneous map. -/
def pushSchemeDegreeOneMap {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) {d : ℕ} {T : Scheme.{u}}
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra (h ≫ g) deg) d T) :
    (Scheme.Modules.pullback (q.morphism ≫ (overHomOf (Z := Z) (Z' := Z') h).left)).obj
        ((pullbackAlgebra g deg).obj (Int.ofNat (1 * d))) ⟶
      RingedSpace.TensorPower.sheaf q.lineBundle 1 :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
      (q.morphism ≫ (overHomOf (Z := Z) (Z' := Z') h).left)).homEquiv
      ((pullbackAlgebra g deg).obj (Int.ofNat (1 * d)))
      (RingedSpace.TensorPower.sheaf q.lineBundle 1)).symm
    (pushSchemePsi (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q 1)

/-- The composite-base homogeneous map preserves the unit. -/
theorem pushSchemePsi_map_one {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    {d : ℕ} {T : Scheme.{u}}
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra (h ≫ g) deg) d T)
    (V : Z.left.Opens) :
    (((pushSchemePsi (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q 0).val.app
      (op V)).hom
      (Eq.mp (RelativeProjDegreeQuadruple.sourceZeroSectionEq (pullbackAlgebra g deg) V d)
        ((pullbackAlgebra g deg).one (op V)))) =
      TensorPower.oneSection T.sheaf q.lineBundle
        (op ((q.morphism ≫ (overHomOf (Z := Z) (Z' := Z') h).left) ⁻¹ᵁ V)) := sorry

/-- The composite-base homogeneous map preserves multiplication. -/
theorem pushSchemePsi_map_mul {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    {d : ℕ} {T : Scheme.{u}}
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra (h ≫ g) deg) d T)
    (V : Z.left.Opens) (i j : ℕ)
    (x : ((pullbackAlgebra g deg).obj (Int.ofNat (i * d))).val.obj (op V))
    (y : ((pullbackAlgebra g deg).obj (Int.ofNat (j * d))).val.obj (op V)) :
    (((pushSchemePsi (Z := Z) (Z' := Z') (T := T) (d := d)
      g h deg hA q (i + j)).val.app (op V)).hom
      (Eq.mp (RelativeProjDegreeQuadruple.sourceMulSectionEq (pullbackAlgebra g deg) V i j d)
        ((pullbackAlgebra g deg).mul (op V) (Int.ofNat (i * d)) (Int.ofNat (j * d)) x y))) =
      TensorPower.mulSection T.sheaf q.lineBundle
        (op ((q.morphism ≫ (overHomOf (Z := Z) (Z' := Z') h).left) ⁻¹ᵁ V)) i j
        (((pushSchemePsi (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q i).val.app
          (op V)).hom x)
        (((pushSchemePsi (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q j).val.app
          (op V)).hom y) := sorry

/-- The chosen degree-one map is the actual adjoint of degree one. -/
theorem pushSchemeDegreeOneMap_spec {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    {d : ℕ} {T : Scheme.{u}}
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra (h ≫ g) deg) d T) :
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (q.morphism ≫ (overHomOf (Z := Z) (Z' := Z') h).left)).homEquiv
      ((pullbackAlgebra g deg).obj (Int.ofNat (1 * d)))
      (RingedSpace.TensorPower.sheaf q.lineBundle 1))
        (pushSchemeDegreeOneMap (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q) =
      pushSchemePsi (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q 1 :=
  Equiv.apply_symm_apply _ _

/-- The actual source comparison transports the degree-one epimorphism. -/
theorem pushSchemeDegreeOneMap_epi {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    {d : ℕ} {T : Scheme.{u}}
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra (h ≫ g) deg) d T) :
    Epi (pushSchemeDegreeOneMap (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q) := sorry

/-- Push a scheme-level quadruple of `(h ≫ g)^* 𝒜` along `h` by composing the
structure morphism and preserving the line bundle and homogeneous maps. -/
def pushSchemeQuadruple {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) {d : ℕ} {T : Scheme.{u}}
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra (h ≫ g) deg) d T) :
    RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d T where
  morphism := q.morphism ≫ (overHomOf (Z := Z) (Z' := Z') h).left
  lineBundle := q.lineBundle
  lineBundle_invertible := q.lineBundle_invertible
  psi := pushSchemePsi (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q
  psi_map_one := pushSchemePsi_map_one (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q
  psi_map_mul := pushSchemePsi_map_mul (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q
  degreeOneMap := pushSchemeDegreeOneMap (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q
  degreeOneMap_spec := pushSchemeDegreeOneMap_spec (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q
  degreeOne_surjective := pushSchemeDegreeOneMap_epi (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q

/-- The structure morphism of `pushSchemeQuadruple` is `q.morphism ≫ (overHomOf (Z := Z) (Z' := Z') h).left`. -/
theorem pushSchemeQuadruple_morphism {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) {d : ℕ} {T : Scheme.{u}}
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra (h ≫ g) deg) d T) :
    (pushSchemeQuadruple (Z := Z) (Z' := Z') (T := T) (d := d) g h deg hA q).morphism = q.morphism ≫ (overHomOf (Z := Z) (Z' := Z') h).left :=
  rfl

/-- The degree-chart component of further base change, sending the specified
universal chart quadruple of the positive-degree chart `d` of `Z'` along `h`
and inverting the association on `Z`. This uses the representing point of
`F_Z'.degreeFunctor d`, not an unspecified global chart choice. -/
noncomputable def furtherDegreeChartMap {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    degreeChartScheme (h ≫ g) deg d ⟶ F_Z.toFunctor.reprX :=
  let q :=
    pushSchemeQuadruple (Z := Z) (Z' := Z')
      (T := degreeChartScheme (h ≫ g) deg d) (d := d.1)
      g h deg hA (universalChartQuadruple (h ≫ g) deg d)
  let y :=
    Classical.choose
      ((F_Z.degreeAssociated d).exists_point (degreeChartScheme (h ≫ g) deg d) q)
  (F_Z.toFunctor.reprW.app (op (degreeChartScheme (h ≫ g) deg d))).inv
    ((F_Z.degreeToFunctor d).app (op (degreeChartScheme (h ≫ g) deg d)) y)

/-- Compatibility of `furtherDegreeChartMap` on overlaps of positive-degree charts. -/
theorem furtherDegreeChartMap_compatible {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)] :
    ∀ d e : { n : ℕ // 1 ≤ n },
      pullback.fst (degreeChartImmersion (h ≫ g) deg d)
          (degreeChartImmersion (h ≫ g) deg e) ≫
        furtherDegreeChartMap g h deg hA d =
      pullback.snd (degreeChartImmersion (h ≫ g) deg d)
          (degreeChartImmersion (h ≫ g) deg e) ≫
        furtherDegreeChartMap g h deg hA e :=
  sorry

/-- The canonical morphism of representing objects
`underline{Proj}_{Z'}((h ≫ g)^* 𝒜) ⟶ underline{Proj}_Z(g^* 𝒜)` induced by a
morphism `h : Z' ⟶ Z` of schemes over `S`, obtained by gluing the specified
degreewise pushalong maps of Lemma 27.16.1. -/
def furtherRelativeProjMap {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)] :
    relativeProjOver (h ≫ g) deg ⟶
      relativeProjOver g deg :=
  Over.homMk
    (Scheme.Cover.glueMorphisms (relativeProjDegreeCover (h ≫ g) deg)
      (furtherDegreeChartMap g h deg F.algebra_isQuasicoherent)
      (furtherDegreeChartMap_compatible g h deg F.algebra_isQuasicoherent))
    sorry

/-- On each positive-degree chart, `furtherRelativeProjMap` agrees with the
representing map of the degreewise base-change isomorphism of Lemma 27.16.1. -/
theorem furtherRelativeProjMap_toPullbackIso {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)]
    (d : { n : ℕ // 1 ≤ n })
    (F'd : Scheme.RelativeProjDegreeFunctorPullback (overHomOf h).left
      (F_Z.degreeFunctor d)) :
    degreeChartImmersion (h ≫ g) deg d ≫
        (furtherRelativeProjMap g h F hF).left =
      furtherDegreeChartMap g h deg F.algebra_isQuasicoherent d :=
  sorry

/-- The morphism `Z' ×_X F ⟶ Z ×_X F` induced by `h : Z' ⟶ Z` over `X`. -/
def pullbackFunctorMap {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (F : ProjFunctor X 𝒜) :
    functorPullback (h ≫ g) F ⟶ functorPullback g F :=
  let hg : (ofOver Z').functorOfPoints ⟶ X.functorOfPoints := h ≫ g
  CategoryTheory.Limits.pullback.lift
    (CategoryTheory.Limits.pullback.fst hg F.baseMap ≫ h)
    (CategoryTheory.Limits.pullback.snd hg F.baseMap) sorry

end RelativeProjBaseChangeData

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
