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
# Base change for relative projective functors of algebraic spaces

This leaf turns explicit pointwise comparison data into a natural isomorphism with the
categorical pullback of functors of points.
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



namespace RelativeProjBaseChangeData

open AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- The positive-degree chart as a scheme over `S`. -/
def degreeChartOver {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) : Over S :=
  Over.mk (degreeChartToBase g deg d ≫ Z.hom)

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

/-- The associated scheme quadruple of the universal point of a positive-degree chart. -/
noncomputable def universalChartQuadruple {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d.1
      ((AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z) d) :=
  (F_Z.degreeAssociated d).representative ((AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z) d)
    (F_Z.degreeFunctor d).toFunctor.reprx

/-- `universalChartQuadruple` is associated to the universal degree-chart point. -/
theorem universalChartQuadruple_spec {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    (F_Z.degreeAssociated d).associated ((AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z) d)
      (F_Z.degreeFunctor d).toFunctor.reprx
      (universalChartQuadruple g deg d) :=
  (F_Z.degreeAssociated d).representative_spec ((AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z) d)
    (F_Z.degreeFunctor d).toFunctor.reprx

/-- The actual pullback/extension comparison for a base-compatible scheme quadruple.
Quasi-coherence is supplied by the original graded algebra hypothesis. -/
def ofSchemePsiSourceIso {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent) {U : Over S} (d : ℕ) (t : U ⟶ Z)
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d U.left)
    (hq : q.morphism = t.left) (n : ℕ) :
    (Modules.RestrictToScheme.extension U).obj
        ((Scheme.Modules.pullback q.morphism).obj
          ((pullbackAlgebra g deg).obj (Int.ofNat (n * d)))) ≅
      (Modules.pullback (ofOverMap t ≫ g)).obj (deg.obj (n * d)) :=
  (Modules.RestrictToScheme.extension U).mapIso
      (eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
        ((pullbackAlgebra g deg).obj (Int.ofNat (n * d)))) hq)) ≪≫
    @Modules.RestrictToScheme.extensionCompositePullbackIso S X U Z g t (deg.obj (n * d))
      (deg.isQuasicoherent hA (n * d))

/-- The pullback-form homogeneous map of a scheme quadruple, as an algebraic-space map. -/
def ofSchemePsi {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent) {U : Over S} (d : ℕ) (t : U ⟶ Z)
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d U.left)
    (hq : q.morphism = t.left) (n : ℕ) :
    (Modules.pullback (ofOverMap t ≫ g)).obj (deg.obj (n * d)) ⟶
      tensorPowerUnit ((Modules.RestrictToScheme.extension U).obj q.lineBundle) n :=
  (ofSchemePsiSourceIso g deg hA d t q hq n).inv ≫
    (Modules.RestrictToScheme.extension U).map
      (((Scheme.Modules.pullbackPushforwardAdjunction q.morphism).homEquiv
          ((pullbackAlgebra g deg).obj (Int.ofNat (n * d)))
          (RingedSpace.TensorPower.sheaf q.lineBundle n)).symm (q.psi n)) ≫
    (Modules.RestrictToScheme.extensionTensorPowerIso U q.lineBundle n).hom

/-- Convert a scheme-level fixed-degree quadruple to an algebraic-space quadruple. -/
def ofSchemeQuadruple {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (hA : 𝒜.IsQuasicoherent) {U : Over S} (d : ℕ) (hd : 1 ≤ d) (t : U ⟶ Z)
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d U.left)
    (hq : q.morphism = t.left) :
    Quadruple 𝒜 deg U := by
  let degree := d
  let positive := hd
  let morphism := ofOverMap t ≫ g
  let lineBundle := (Modules.RestrictToScheme.extension U).obj q.lineBundle
  let psi := ofSchemePsi g deg hA d t q hq
  let degreeOneMap := ofSchemePsi g deg hA d t q hq 1
  have laws :
    (isInvertibleObject lineBundle) ∧
    (Modules.structureModulePullbackInv morphism ≫
        (Modules.pullback morphism).map (degreeZeroUnit deg) ≫
          eqToHom
              (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                (Nat.zero_mul degree).symm) ≫
            psi 0 =
      eqToHom (tensorPowerUnit_zero lineBundle).symm) ∧
    (∀ i j : ℕ,
      pullbackTensorLax morphism (deg.obj (i * degree)) (deg.obj (j * degree)) ≫
          (Modules.pullback morphism).map (deg.mul (i * degree) (j * degree)) ≫
            eqToHom
                (congrArg (fun k : ℕ ↦ (Modules.pullback morphism).obj (deg.obj k))
                  (Nat.add_mul i j degree).symm) ≫
              psi (i + j) =
        tensorHom (psi i) (psi j) ≫ (tensorPowerUnitAddIso lineBundle i j).hom) ∧
    (degreeOneMap = psi 1) ∧
    (Epi degreeOneMap) := by sorry
  exact {
    degree := degree
    positive := positive
    morphism := morphism
    lineBundle := lineBundle
    psi := psi
    degreeOneMap := degreeOneMap
    lineBundle_invertible := laws.1
    psi_map_one := laws.2.1
    psi_map_mul := laws.2.2.1
    degreeOneMap_spec := laws.2.2.2.1
    degreeOne_surjective := laws.2.2.2.2
  }

/-- The line bundle of `ofSchemeQuadruple` is the extension of the scheme-level line bundle. -/
theorem ofSchemeQuadruple_lineBundle {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) {U : Over S} (d : ℕ) (hd : 1 ≤ d)
    (t : U ⟶ Z)
    (q : RelativeProjDegreeQuadruple (pullbackAlgebra g deg) d U.left)
    (hq : q.morphism = t.left) :
    (ofSchemeQuadruple g deg hA d hd t q hq).lineBundle =
      (Modules.RestrictToScheme.extension U).obj q.lineBundle :=
  rfl

/-- The morphism of a positive-degree chart into `underline{Proj}_Z(g^* 𝒜)`. -/
def degreeChartToRelativeProj {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    degreeChartOver g deg d ⟶ relativeProjOver g deg :=
  Over.homMk ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z)) d) sorry

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
      ((AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z) (chartIndexOfOpens g deg V))
      (openOver (relativeProjOver g deg) V).left
      F_Z.toFunctor.reprX
      ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z)) (chartIndexOfOpens g deg V))
      (openOverι (relativeProjOver g deg) V).left
      ((AlgebraicGeometry.RelativeProjFunctor.degreeMap_isOpenImmersion (F := F_Z)) (chartIndexOfOpens g deg V))
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
    (ProjFunctor.QcCompatibleSystem.mk
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
      (Modules.restrictToScheme T).obj (tensorPowerUnit q.lineBundle n) :=
  @Modules.RestrictToScheme.tensorPowerIso S T q.lineBundle
    (Modules.RestrictToScheme.invertible_isQuasicoherent T q.lineBundle q.lineBundle_invertible) n

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

/-- The epi transports through QCoh comparison; the algebra hypothesis is the graded algebra’s. -/
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
  let y := (F_Z.degreeAssociated ⟨q.degree, q.positive⟩).pointOf T.left (toSchemeQuadruple (T := T) g deg hA t q hq)
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
      ((F_Z.degreeAssociated ⟨q.degree, q.positive⟩).pointOf T.left (toSchemeQuadruple (T := T) g deg hA t q hq))
      (toSchemeQuadruple (T := T) g deg hA t q hq) :=
  (F_Z.degreeAssociated ⟨q.degree, q.positive⟩).pointOf_spec T.left (toSchemeQuadruple (T := T) g deg hA t q hq)

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

/-- Canonical comparison data from chartwise pushalong of universal chart quadruples
`(d, f, L, ψ) ↦ (d, g ∘ f, L, ψ)` along the positive-degree cover. -/
noncomputable def ofPushalong {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    RelativeProjBaseChangeData g F deg hF := by
  have laws : ∀ (T : Over S) (t : (ofOver Z).functorOfPoints.obj (op T)),
      Function.LeftInverse (SchemeQcSystem.glue (baseMap := relativeProjStructureMap g deg))
        (SchemeQcSystem.ofPoint (baseMap := relativeProjStructureMap g deg) (t := t)) ∧
      Function.RightInverse (SchemeQcSystem.glue (baseMap := relativeProjStructureMap g deg))
        (SchemeQcSystem.ofPoint (baseMap := relativeProjStructureMap g deg) (t := t)) := by sorry
  exact {
    schemeQcLimit := fun T t ↦ {
      toFun := SchemeQcSystem.ofPoint
      invFun := SchemeQcSystem.glue
      left_inv := (laws T t).1
      right_inv := (laws T t).2 }
    schemeQcLimit_restrict := fun T t x V _ ↦ rfl }

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
      (F_Z.degreeAssociated ⟨q.degree, q.positive⟩).associated T.left
        ((F_Z.degreeAssociated ⟨q.degree, q.positive⟩).pointOf T.left
          (toSchemeQuadruple g deg F.algebra_isQuasicoherent t q hq))
        (toSchemeQuadruple g deg F.algebra_isQuasicoherent t q hq)) ∧
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
      F.pointOver (op T) (g.app (op T) t) := by
  let Source := schemePointOver F_Z (relativeProjStructureMap g deg) (op T) t
  let Target := F.pointOver (op T) (g.app (op T) t)
  let forward := fun x : Source ↦ pointOfPulledDegreeCover (hF := hF) t x
  let ForwardLaw := ∀ x : Source, F.baseMap.app (op T) (forward x) = g.app (op T) t
  let InverseLaw := ∀ y : Target, (hF.quadrupleOf T y.1).morphism = ofOverMap t ≫ g
  let backward := fun (hi : InverseLaw) (y : Target) ↦
    schemePointOfQuadruple g deg F.algebra_isQuasicoherent T t (hF.quadrupleOf T y.1) (hi y)
  have laws : ForwardLaw ∧ InverseLaw ∧ ∀ (hf : ForwardLaw) (hi : InverseLaw),
      Function.LeftInverse (backward hi) (fun x ↦ (⟨forward x, hf x⟩ : Target)) ∧
      Function.RightInverse (backward hi) (fun x ↦ (⟨forward x, hf x⟩ : Target)) := by sorry
  exact {
    toFun := fun x ↦ ⟨forward x, laws.1 x⟩
    invFun := backward laws.2.1
    left_inv := (laws.2.2 laws.1 laws.2.1).1
    right_inv := (laws.2.2 laws.1 laws.2.1).2 }

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
    schemePointOver F_Z (relativeProjStructureMap g deg) T t ≃ F.pointOver T (g.app T t) := by
  let Source := schemePointOver F_Z (relativeProjStructureMap g deg) T t
  let Target := F.pointOver T (g.app T t)
  let forward := fun x : Source ↦ pointOfPulledDegreeCover (hF := hF) t x
  let ForwardLaw := ∀ x : Source, F.baseMap.app T (forward x) = g.app T t
  let values := fun (y : Target) (V : T.unop.left.Opens) (_ : CompactSpace V.toScheme) ↦
    let a := op (openOverι T.unop V)
    let tV := (ofOver Z).functorOfPoints.map a t
    let yV : F.pointOver (op (openOver T.unop V)) (g.app (op (openOver T.unop V)) tV) :=
      ⟨F.toFunctor.map a y.1, by
        exact (ConcreteCategory.congr_hom (F.baseMap.naturality a) y.1).trans
          ((congrArg (X.functorOfPoints.map a) y.2).trans
            (ConcreteCategory.congr_hom (g.naturality a) t).symm)⟩
    (data.pointEquivQc (openOver T.unop V) tV).symm yV
  let Compatible := ∀ (y : Target) (V W : T.unop.left.Opens)
      [cV : CompactSpace V.toScheme] [cW : CompactSpace W.toScheme] (hle : V ≤ W),
    F_Z.toFunctor.map (op (openOverιLE T.unop hle).left) (values y W cW).1 = (values y V cV).1
  let backward := fun (hc : Compatible) (y : Target) ↦
    (data.schemeQcLimit T.unop t).symm {
      restrict := fun V cV ↦ values y V cV
      compatible := hc y }
  have laws : ForwardLaw ∧ Compatible ∧ ∀ (hf : ForwardLaw) (hc : Compatible),
      Function.LeftInverse (backward hc) (fun x ↦ (⟨forward x, hf x⟩ : Target)) ∧
      Function.RightInverse (backward hc) (fun x ↦ (⟨forward x, hf x⟩ : Target)) := by sorry
  exact {
    toFun := fun x ↦ ⟨forward x, laws.1 x⟩
    invFun := backward laws.2.1
    left_inv := (laws.2.2 laws.1 laws.2.1).1
    right_inv := (laws.2.2 laws.1 laws.2.1).2 }

/-- The constructed fiber equivalences are natural in the test scheme. -/
theorem pointEquiv_natural {Z : Over S} {g : ofOver Z ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (data : RelativeProjBaseChangeData g F deg hF)
    {T T' : (Over S)ᵒᵖ} (a : T ⟶ T')
    (t : (ofOver Z).functorOfPoints.obj T)
    (x : schemePointOver F_Z (relativeProjStructureMap g deg) T t) :
    (data.pointEquiv T' ((ofOver Z).functorOfPoints.map a t)
        ⟨F_Z.toFunctor.map (op a.unop.left) x.1, by
          change (relativeProjStructureMap g deg).app (op T'.unop.left)
            (F_Z.toFunctor.map (op a.unop.left) x.1) = a.unop.left ≫ t.left
          have hn := (relativeProjStructureMap g deg).naturality
            (show op T.unop.left ⟶ op T'.unop.left from op a.unop.left)
          exact (ConcreteCategory.congr_hom hn x.1).trans
            (congrArg (fun f : T.unop.left ⟶ Z.left ↦ a.unop.left ≫ f) x.2)⟩).1 =
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
      (pullbackAlgebra (h ≫ g) deg).obj (Int.ofNat n) :=
  @Modules.RestrictToScheme.compositePullbackIso S X Z' Z g
    (overHomOf (Z := Z) (Z' := Z') h) (deg.obj n) (deg.isQuasicoherent hA n) ≪≫
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
    (AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z') d ⟶ F_Z.toFunctor.reprX :=
  let q :=
    pushSchemeQuadruple (Z := Z) (Z' := Z')
      (T := (AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z') d) (d := d.1)
      g h deg hA (universalChartQuadruple (h ≫ g) deg d)
  let y := (F_Z.degreeAssociated d).pointOf
    ((AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z') d) q
  (F_Z.toFunctor.reprW.app (op ((AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z') d))).inv
    ((F_Z.degreeToFunctor d).app (op ((AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z') d)) y)

/-- Compatibility of `furtherDegreeChartMap` on overlaps of positive-degree charts. -/
theorem furtherDegreeChartMap_compatible {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)] :
    ∀ d e : { n : ℕ // 1 ≤ n },
      pullback.fst ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z')) d)
          ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z')) e) ≫
        furtherDegreeChartMap g h deg hA d =
      pullback.snd ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z')) d)
          ((AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z')) e) ≫
        furtherDegreeChartMap g h deg hA e :=
  sorry

/-- The canonical morphism of representing objects
`underline{Proj}_{Z'}((h ≫ g)^* 𝒜) ⟶ underline{Proj}_Z(g^* 𝒜)` induced by a
morphism `h : Z' ⟶ Z` of schemes over `S`, obtained by gluing the specified
degreewise pushalong maps. -/
def furtherRelativeProjMap {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)] :
    relativeProjOver (h ≫ g) deg ⟶
      relativeProjOver g deg :=
  Over.homMk
    (Scheme.Cover.glueMorphisms ((AlgebraicGeometry.RelativeProjFunctor.degreeCover (F := F_Z')))
      (furtherDegreeChartMap g h deg F.algebra_isQuasicoherent)
      (furtherDegreeChartMap_compatible g h deg F.algebra_isQuasicoherent))
    sorry

/-- Restricting the further-base-change morphism to a positive-degree chart gives the
map classifying the pushed universal quadruple on that chart. -/
theorem furtherRelativeProjMap_toPullbackIso {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)]
    (d : { n : ℕ // 1 ≤ n }) :
    (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z')) d ≫
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

/-- The structural map of a relative projective functor associated to quadruples is
representable. -/
theorem baseMap_relativelyRepresentable {𝒜} (F : ProjFunctor X 𝒜)
    (deg : DegreePieces 𝒜) (hF : F.IsAssociatedToQuadruples deg) :
    yoneda.relativelyRepresentable F.baseMap :=
  sorry

/-- The algebraic space over `S` whose functor of points is a relative projective functor
associated to quadruples. -/
def toAlgebraicSpace {𝒜} (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) : AlgebraicSpace S :=
  ofRelativelyRepresentable F.baseMap (baseMap_relativelyRepresentable F deg hF)

/-- The functor of points of `toAlgebraicSpace F hF` is the underlying functor of `F`. -/
theorem toAlgebraicSpace_functorOfPoints {𝒜} (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg) :
    (toAlgebraicSpace F hF).functorOfPoints = F.toFunctor :=
  sorry

/-- The structure morphism `π : toAlgebraicSpace F ⟶ X` is the stored base map of `F`. -/
def toAlgebraicSpace_hom {𝒜} (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    toAlgebraicSpace F hF ⟶ X :=
  ofRelativelyRepresentable_hom F.baseMap (baseMap_relativelyRepresentable F deg hF)

/-- `toAlgebraicSpace_hom F hF` is the stored base map of `F`. -/
theorem toAlgebraicSpace_hom_eq {𝒜} (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    toAlgebraicSpace_hom F hF = F.baseMap :=
  sorry


/-- The fibre product `Z ×_X F` as an algebraic space. -/
def pullbackOverSpace {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg) :
    AlgebraicSpace S :=
  pullbackOver g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal

/-- The functor of points of `pullbackOverSpace g F hF` is the categorical pullback of
`g` and `F.baseMap`. -/
theorem pullbackOverSpace_functorOfPoints {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    (pullbackOverSpace g F hF).functorOfPoints = functorPullback g F :=
  rfl

/-- For a morphism `g : Z ⟶ X` with `Z` a scheme, there is a
canonical isomorphism `underline{Proj}_Z(g^* 𝒜) = Z ×_X F`. -/
@[stacks 084B]
def baseChangeIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    ofOver (relativeProjOver g deg) ≅ pullbackOverSpace g F hF where
  hom := (RelativeProjBaseChangeData.ofPushalong g F hF).toPullbackIso'.hom
  inv := (RelativeProjBaseChangeData.ofPushalong g F hF).toPullbackIso'.inv
  hom_inv_id :=
    (RelativeProjBaseChangeData.ofPushalong g F hF).toPullbackIso'.hom_inv_id
  inv_hom_id :=
    (RelativeProjBaseChangeData.ofPushalong g F hF).toPullbackIso'.inv_hom_id

/-- The isomorphism `underline{Proj}_Z(g^* 𝒜) ≅ Z ×_X F` commutes with the structure
maps to `Z`. -/
theorem baseChangeIso_fst {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    (baseChangeIso g F hF).hom ≫
        pullbackOverFst g (toAlgebraicSpace_hom F hF) X.isSheaf
          X.representableDiagonal =
      yoneda.map (relativeProjToZ g deg) :=
  sorry

/-- The morphism `Z' ×_X F ⟶ Z ×_X F` induced by a morphism of schemes `h : Z' ⟶ Z`
over `X`. -/
def pullbackOverSpaceMap {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z) (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg) :
    pullbackOverSpace (h ≫ g) F hF ⟶ pullbackOverSpace g F hF :=
  RelativeProjBaseChangeData.pullbackFunctorMap g h F

/-- The canonical isomorphism is compatible with further base
change along a morphism of schemes over `S`. -/
@[stacks 084B]
theorem baseChangeIso_comp {Z Z' : Over S} (g : ofOver Z ⟶ X)
    (h : ofOver Z' ⟶ ofOver Z)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [F_Z' : AlgebraicGeometry.RelativeProjFunctor Z'.left
      (pullbackAlgebra (h ≫ g) deg)] :
    (baseChangeIso (h ≫ g) F hF).hom ≫
        pullbackOverSpaceMap g h F hF =
      ofOverMap (RelativeProjBaseChangeData.furtherRelativeProjMap g h F hF) ≫
        (baseChangeIso g F hF).hom :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.RelativeProj
