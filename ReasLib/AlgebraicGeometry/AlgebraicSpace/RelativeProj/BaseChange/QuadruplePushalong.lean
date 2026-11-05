/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange.SchemeGluing

/-!
# Quadruple pushalong for relative Proj base change

Universal chart quadruples, transport in both directions, and comparison data.
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

end RelativeProjBaseChangeData

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
