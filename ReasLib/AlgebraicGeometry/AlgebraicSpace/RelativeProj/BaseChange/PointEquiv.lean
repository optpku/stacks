/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange.QuadruplePushalong

/-!
# Point equivalences for relative Proj base change

Comparison on test schemes and compatibility with further scheme base change.
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

namespace RelativeProjBaseChangeData

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

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
