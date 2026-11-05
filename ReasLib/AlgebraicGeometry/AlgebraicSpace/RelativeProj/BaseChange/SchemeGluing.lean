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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.QuadrupleFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.ExtensionComposition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.PullbackAlgebra

/-!
# Scheme gluing for relative Proj base change

Pointwise base change and gluing scheme-level points on quasi-compact opens.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules SheafOfModules.RingedSite
open AlgebraicGeometry.AlgebraicSpace.ReasLibPullback
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

/-- The structure map of a positive-degree chart to `Z.left`, obtained from
`degreeFunctor.baseMap` at the universal point. -/
def degreeChartToBase {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    (AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z) d ⟶ Z.left :=
  (F_Z.degreeFunctor d).baseMap.app (op ((AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z) d))
    (F_Z.degreeFunctor d).toFunctor.reprx

/-- Compatibility of the chart structure maps on overlaps. -/
theorem degreeChartToBase_compatible {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    ∀ d e : { n : ℕ // 1 ≤ n },
      pullback.fst ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z)) d) ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z)) e) ≫
          degreeChartToBase g deg d =
        pullback.snd ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z)) d) ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z)) e) ≫
          degreeChartToBase g deg e :=
  sorry

/-- The scheme morphism `underline{Proj}_Z(g^* 𝒜) ⟶ Z.left` obtained by gluing the
positive-degree chart structure maps. -/
def relativeProjToZLeft {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    F_Z.toFunctor.reprX ⟶ Z.left :=
  Scheme.Cover.glueMorphisms ((AlgebraicGeometry.RelativeProjFunctor.degreeCover (F := F_Z)))
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

/-- A scheme-level point determines its restrictions to all quasi-compact opens. -/
def ofPoint {Z : Over S} {𝒜Z : GradedAlgebraSheaf.{u, u} Z.left.sheaf}
    {F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left 𝒜Z}
    {baseMap : F_Z.toFunctor ⟶ yoneda.obj Z.left} {T : Over S}
    {t : (ofOver Z).functorOfPoints.obj (op T)}
    (x : schemePointOver F_Z baseMap (op T) t) : SchemeQcSystem F_Z baseMap t := by
  let restrict : ∀ (V : T.left.Opens) [CompactSpace V.toScheme],
      schemePointOver F_Z baseMap (op (openOver T V))
        ((ofOver Z).functorOfPoints.map (op (openOverι T V)) t) := fun V _ ↦
    ⟨F_Z.toFunctor.map (op (openOverι T V).left) x.1, by
      exact (ConcreteCategory.congr_hom (baseMap.naturality (op (openOverι T V).left)) x.1).trans
        (congrArg (fun f : T.left ⟶ Z.left ↦ (openOverι T V).left ≫ f) x.2)⟩
  have laws : ∀ (V W : T.left.Opens) [CompactSpace V.toScheme] [CompactSpace W.toScheme]
      (hle : V ≤ W),
      F_Z.toFunctor.map (op (openOverιLE T hle).left) (restrict W).1 = (restrict V).1 := by sorry
  exact ⟨restrict, laws⟩

/-- The compatible system of a scheme-level point consists of its restrictions to
quasi-compact opens, and these restrictions agree along inclusions. -/
theorem ofPoint_spec {Z : Over S} {𝒜Z : GradedAlgebraSheaf.{u, u} Z.left.sheaf}
    {F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left 𝒜Z}
    {baseMap : F_Z.toFunctor ⟶ yoneda.obj Z.left} {T : Over S}
    {t : (ofOver Z).functorOfPoints.obj (op T)}
    (x : schemePointOver F_Z baseMap (op T) t) :
    (∀ (V : T.left.Opens) [CompactSpace V.toScheme],
      ((ofPoint x).restrict V).1 = F_Z.toFunctor.map (op (openOverι T V).left) x.1) ∧
    (∀ (V W : T.left.Opens) [CompactSpace V.toScheme] [CompactSpace W.toScheme]
        (hle : V ≤ W),
      F_Z.toFunctor.map (op (openOverιLE T hle).left) ((ofPoint x).restrict W).1 =
        ((ofPoint x).restrict V).1) := sorry

/-- A compatible system is glued by gluing its representing morphisms on affine opens. -/
def glue {Z : Over S} {𝒜Z : GradedAlgebraSheaf.{u, u} Z.left.sheaf}
    {F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left 𝒜Z}
    {baseMap : F_Z.toFunctor ⟶ yoneda.obj Z.left} {T : Over S}
    {t : (ofOver Z).functorOfPoints.obj (op T)}
    (s : SchemeQcSystem F_Z baseMap t) : schemePointOver F_Z baseMap (op T) t := by
  let cover := T.left.openCoverOfIsOpenCover (fun V : T.left.affineOpens ↦ V.1)
    (iSup_affineOpens_eq_top T.left)
  let maps : ∀ V : T.left.affineOpens, cover.X V ⟶ F_Z.toFunctor.reprX :=
    fun V ↦ (F_Z.toFunctor.reprW.app (op V.1.toScheme)).inv (s.restrict V.1).1
  let Compatible : Prop := ∀ V W,
    pullback.fst (cover.f V) (cover.f W) ≫ maps V =
      pullback.snd (cover.f V) (cover.f W) ≫ maps W
  have laws : Compatible ∧ ∀ hc : Compatible,
      baseMap.app (op T.left)
        ((F_Z.toFunctor.reprW.app (op T.left)).hom (cover.glueMorphisms maps hc)) = t.left := by sorry
  exact ⟨(F_Z.toFunctor.reprW.app (op T.left)).hom
    (cover.glueMorphisms maps laws.1), laws.2 laws.1⟩

end SchemeQcSystem

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
