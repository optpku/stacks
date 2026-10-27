/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Psi
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineModel
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineSectionRing.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Quasicoherent

/-!
# Scheme comparison of canonical relative-Proj twists

The canonical homogeneous maps are compared on affine opens and positive-degree
charts after arbitrary scheme base change.
-/
@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
open scoped DirectSum
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {deg : DegreePieces 𝒜}


/-- The projection `underline{Proj}_Z(g^* 𝒜) ⟶ underline{Proj}_X(𝒜)` induced by
`baseChangeIso` and the second fibre-product projection. -/
def toRelativeProj {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    ofOver (relativeProjOver g deg) ⟶ toAlgebraicSpace F hF :=
  (baseChangeIso g F hF).hom ≫
    AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOverSnd g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal

/-- The fibre-product square: `toRelativeProj` lies over `g`. -/
theorem toRelativeProj_comp {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)] :
    toRelativeProj g F hF ≫ toAlgebraicSpace_hom F hF =
      ofOverMap (relativeProjToZ g deg) ≫ g :=
  sorry

/-- Pullback of `psi.hom n` along the scheme-level projection to `P`. -/
def psi_baseChange_hom {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (n : ℕ) :
    (Modules.pullback (toRelativeProj g F hF)).obj
      ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)) ⟶
    (Modules.pullback (toRelativeProj g F hF)).obj (obj F hF n) :=
  (Modules.pullback (toRelativeProj g F hF)).map ((psi F hF).hom n)

/-- Transport `psi.hom n` across the fibre-product square to a map out of
`π_Z^* (g^* 𝒜_n)`. -/
def psi_pullback {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (n : ℕ) :
    (Modules.pullback (ofOverMap (relativeProjToZ g deg))).obj
      ((Modules.pullback g).obj (deg.obj n)) ⟶
    (Modules.pullback (toRelativeProj g F hF)).obj (obj F hF n) :=
  (Modules.pullbackCompIso (ofOverMap (relativeProjToZ g deg)) g).hom.app (deg.obj n) ≫
    eqToHom (congrArg (fun f ↦ (Modules.pullback f).obj (deg.obj n))
      (toRelativeProj_comp g F hF).symm) ≫
    (Modules.pullbackCompIso (toRelativeProj g F hF)
        (toAlgebraicSpace_hom F hF)).inv.app (deg.obj n) ≫
      psi_baseChange_hom g F hF n

/-- The canonical affine scheme chart map of `g^* 𝒜`: the homogeneous
pullback map of the affine section algebra of `pullbackAlgebra g deg`. -/
def schemeChartPsi {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    [hA : (pullbackAlgebra g deg).IsCommutative] [IsAffine Z.left] (n : ℕ) :
    (Scheme.Modules.pullback
      (Scheme.RelativeProjAffineSectionRing.toBase (pullbackAlgebra g deg))).obj
      ((pullbackAlgebra g deg).obj (n : ℤ)) ⟶
    Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg)) (n : ℤ) :=
  Scheme.RelativeProjAffineSectionRing.homogeneousPullbackMap
    (pullbackAlgebra g deg)
    (pullbackAlgebra_isQuasicoherent g deg F.algebra_isQuasicoherent) n

/-- The classifying map of a positive-degree chart of `underline{Proj}_Z(g^* 𝒜)`
into the affine section-algebra Proj. -/
def degreeChartSection {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [hA : (pullbackAlgebra g deg).IsCommutative] [IsAffine Z.left] (d : { n : ℕ // 1 ≤ n }) :
    AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z d ⟶
      Scheme.RelativeProjAffineSectionRing.scheme (pullbackAlgebra g deg) :=
  (Scheme.RelativeProjAffineSectionRing.degreeAssociated (pullbackAlgebra g deg)
      (pullbackAlgebra_isQuasicoherent g deg F.algebra_isQuasicoherent) d.2).pointOf
      (AlgebraicGeometry.RelativeProjFunctor.degreeScheme F_Z d)
      (RelativeProjBaseChangeData.universalChartQuadruple g deg d) ≫
    (Proj.degreeOpen
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg)) d.1).ι

/-- Degree-chart classifying maps agree on overlaps, so they glue over `P_Z`. -/
theorem degreeChartSection_compatible {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [hA : (pullbackAlgebra g deg).IsCommutative] [IsAffine Z.left] :
    ∀ d e : { n : ℕ // 1 ≤ n },
      pullback.fst (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z) d) (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z) e) ≫
          degreeChartSection g F d =
        pullback.snd (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z) d) (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := F_Z) e) ≫
          degreeChartSection g F e :=
  sorry

/-- The classifying section `underline{Proj}_Z(g^* 𝒜) ⟶ Proj(Γ(Z, g^* 𝒜))` of the
affine section-algebra model. -/
def schemeSectionMap {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [hA : (pullbackAlgebra g deg).IsCommutative] [IsAffine Z.left] :
    F_Z.toFunctor.reprX ⟶
      Scheme.RelativeProjAffineSectionRing.scheme (pullbackAlgebra g deg) :=
  Scheme.Cover.glueMorphisms (AlgebraicGeometry.RelativeProjFunctor.degreeCover (F := F_Z))
    (degreeChartSection g F) (degreeChartSection_compatible g F)

/-- The classifying section lies over `π_Z`. -/
theorem schemeSectionMap_toBase {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [hA : (pullbackAlgebra g deg).IsCommutative] [IsAffine Z.left] :
    schemeSectionMap g F hF ≫
        Scheme.RelativeProjAffineSectionRing.toBase (pullbackAlgebra g deg) =
      relativeProjToZLeft g deg :=
  sorry

/-- The canonical affine scheme chart formula on `P_Z`: pull `homogeneousPullbackMap` back along
the classifying section. -/
def schemeLocalPsi {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [hA : (pullbackAlgebra g deg).IsCommutative] [IsAffine Z.left] (n : ℕ) :
    (Scheme.Modules.pullback (schemeSectionMap g F hF)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase (pullbackAlgebra g deg))).obj
        ((pullbackAlgebra g deg).obj (n : ℤ))) ⟶
    (Scheme.Modules.pullback (schemeSectionMap g F hF)).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg))
        (n : ℤ)) :=
  (Scheme.Modules.pullback (schemeSectionMap g F hF)).map (schemeChartPsi g F n)

/-- Identify the iterated pullback along `schemeSectionMap` and `toBase` with pullback
along `π_Z`, using `schemeSectionMap_toBase`. -/
def schemeLocalPsiSourceIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [hA : (pullbackAlgebra g deg).IsCommutative] [IsAffine Z.left] (n : ℕ) :
    (Scheme.Modules.pullback (schemeSectionMap g F hF)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase (pullbackAlgebra g deg))).obj
        ((pullbackAlgebra g deg).obj (n : ℤ))) ≅
    (Scheme.Modules.pullback (relativeProjToZLeft g deg)).obj
      ((pullbackAlgebra g deg).obj (n : ℤ)) :=
  (Scheme.Modules.pullbackComp (schemeSectionMap g F hF)
      (Scheme.RelativeProjAffineSectionRing.toBase (pullbackAlgebra g deg))).app
    ((pullbackAlgebra g deg).obj (n : ℤ)) ≪≫
  (Scheme.Modules.pullbackCongr (schemeSectionMap_toBase g F hF)).app
    ((pullbackAlgebra g deg).obj (n : ℤ))

/-- Restriction/pullback comparison identifying `π_Z^* (g^* 𝒜_n)` on the scheme `P_Z`
with the algebraic-space pullback source of `psi_pullback`. -/
def schemePsiSourceComparison {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (n : ℕ) :
    (Scheme.Modules.pullback (relativeProjToZLeft g deg)).obj
      ((pullbackAlgebra g deg).obj (n : ℤ)) ⟶
    (Modules.restrictToScheme (relativeProjOver g deg)).obj
      ((Modules.pullback (ofOverMap (relativeProjToZ g deg))).obj
        ((Modules.pullback g).obj (deg.obj n))) :=
  eqToHom (congrArg (fun M ↦ (Scheme.Modules.pullback (relativeProjToZLeft g deg)).obj M)
      (pullbackAlgebra_obj_ofNat g deg n)) ≫
    Modules.RestrictToScheme.pullbackComparison (relativeProjToZ g deg)
      ((Modules.pullback g).obj (deg.obj n))

/-- Restriction of `psi_pullback` to the underlying scheme of `underline{Proj}_Z(g^* 𝒜)`. -/
def psi_pullback_restrict {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (n : ℕ) :
    (Modules.restrictToScheme (relativeProjOver g deg)).obj
      ((Modules.pullback (ofOverMap (relativeProjToZ g deg))).obj
        ((Modules.pullback g).obj (deg.obj n))) ⟶
    (Modules.restrictToScheme (relativeProjOver g deg)).obj
      ((Modules.pullback (toRelativeProj g F hF)).obj (obj F hF n)) :=
  (Modules.restrictToScheme (relativeProjOver g deg)).map (psi_pullback g F hF n)

/-- The affine open `U ⊂ Z` as a scheme over `S`. -/
def affineOpenOver {Z : Over S} (U : Z.left.affineOpens) : Over S :=
  openOver Z (U : Z.left.Opens)

/-- The underlying scheme of `affineOpenOver U` is the affine open `U`. -/
theorem affineOpenOver_left {Z : Over S} (U : Z.left.affineOpens) :
    (affineOpenOver U).left = (U : Z.left.Opens).toScheme :=
  rfl

/-- An affine open of `Z` is an affine scheme. -/
instance affineOpenOver_isAffine {Z : Over S} (U : Z.left.affineOpens) :
    IsAffine (affineOpenOver U).left :=
  inferInstanceAs (IsAffine U)

/-- The restricted morphism `U ⟶ X` associated to `g : Z ⟶ X`. -/
def affineOpenHom {Z : Over S} (g : ofOver Z ⟶ X) (U : Z.left.affineOpens) :
    ofOver (affineOpenOver U) ⟶ X :=
  ofOverMap (openOverι Z (U : Z.left.Opens)) ≫ g

/-- Affine-open restriction of `g^* 𝒜`. This recovers `pullbackAlgebra g deg` when
`U` is the top open of an affine scheme `Z`. -/
abbrev affineOpenAlgebra {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (U : Z.left.affineOpens) :
    GradedAlgebraSheaf.{u, u} (affineOpenOver U).left.sheaf :=
  pullbackAlgebra (affineOpenHom g U) deg

/-- Quasi-coherence of the affine-open restriction. -/
theorem affineOpenAlgebra_isQuasicoherent {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (F : ProjFunctor X 𝒜) (U : Z.left.affineOpens) :
    (affineOpenAlgebra g deg U).IsQuasicoherent :=
  pullbackAlgebra_isQuasicoherent (affineOpenHom g U) deg F.algebra_isQuasicoherent

/-- Commutativity of the affine-open restriction, from the source algebra. -/
def affineOpenAlgebra_isCommutative {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (F : ProjFunctor X 𝒜) (U : Z.left.affineOpens) :
    (affineOpenAlgebra g deg U).IsCommutative :=
  @pullbackAlgebra_isCommutative _ _ _ _ (affineOpenHom g U) deg F.algebra_isCommutative

/-- The canonical affine relative-Proj model of the restricted algebra. -/
def affineOpenProj {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (F : ProjFunctor X 𝒜) (U : Z.left.affineOpens) :
    AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U) :=
  @Scheme.RelativeProjAffineSectionRing.model _ (affineOpenAlgebra g deg U)
    (affineOpenAlgebra_isCommutative g deg F U) (affineOpenOver_isAffine U)
    (affineOpenAlgebra_isQuasicoherent g deg F U)

/-- The classifying section of a positive-degree chart of
`underline{Proj}_U(g^* 𝒜|_U)` into the affine section-algebra model `Proj Γ(U, g^* 𝒜)`. -/
def affineChartSection {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) :
    AlgebraicGeometry.RelativeProjFunctor.degreeScheme (affineOpenProj g deg F U) d ⟶
      Scheme.RelativeProjAffineSectionRing.scheme (affineOpenAlgebra g deg U) :=
  degreeChartSection (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F d

/-- The classifying section of the chart lies over `U`. -/
theorem affineChartSection_toBase {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) :
    affineChartSection g F hF U d ≫
        Scheme.RelativeProjAffineSectionRing.toBase (affineOpenAlgebra g deg U) =
      degreeChartToBase (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg d :=
  sorry

/-- A positive-degree chart of `underline{Proj}_U(g^* 𝒜|_U)` lies over `U`. -/
theorem affineChartImmersion_toBase {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜)
    (U : Z.left.affineOpens)
    (d : { n : ℕ // 1 ≤ n }) :
    AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d ≫
        relativeProjToZLeft (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg =
      degreeChartToBase (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg d :=
  sorry

/-- The glued classifying section restricts to `affineChartSection` on a
positive-degree chart. -/
theorem affineChartSectionMap_comp {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) :
    AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d ≫
        schemeSectionMap (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF =
      affineChartSection g F hF U d :=
  sorry

/-- Source comparison of the canonical affine chart formula: iterated pullback along the
classifying section and `toBase` identifies with pullback along the chart
structure map to `U`. -/
def affineChartSourceIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase (affineOpenAlgebra g deg U))).obj
        ((affineOpenAlgebra g deg U).obj (n : ℤ))) ≅
    (Scheme.Modules.pullback (degreeChartToBase (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg d)).obj
      ((affineOpenAlgebra g deg U).obj (n : ℤ)) :=
  (Scheme.Modules.pullbackComp (affineChartSection g F hF U d)
      (Scheme.RelativeProjAffineSectionRing.toBase (affineOpenAlgebra g deg U))).app
    ((affineOpenAlgebra g deg U).obj (n : ℤ)) ≪≫
  (Scheme.Modules.pullbackCongr (affineChartSection_toBase g F hF U d)).app
    ((affineOpenAlgebra g deg U).obj (n : ℤ))

/-- Source transport from `π_U^* (g^* 𝒜_n)` on a positive-degree chart to the
algebraic-space pullback source of `psi_pullback`. -/
def affineChartPsiSourceComparison {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback (degreeChartToBase (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg d)).obj
      ((affineOpenAlgebra g deg U).obj (n : ℤ)) ⟶
    (Scheme.Modules.pullback (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d)).obj
      ((Modules.restrictToScheme (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
        ((Modules.pullback (ofOverMap (relativeProjToZ (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg))).obj
          ((Modules.pullback (affineOpenHom g U)).obj (deg.obj n)))) :=
  (Scheme.Modules.pullbackCongr (affineChartImmersion_toBase g F U d)).inv.app
    ((affineOpenAlgebra g deg U).obj (n : ℤ)) ≫
  (Scheme.Modules.pullbackComp (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d)
      (relativeProjToZLeft (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).inv.app
    ((affineOpenAlgebra g deg U).obj (n : ℤ)) ≫
  (Scheme.Modules.pullback (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d)).map
    (schemePsiSourceComparison (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF n)

/-- Restriction of `psi_pullback` to a positive-degree chart of
`underline{Proj}_U(g^* 𝒜|_U)`. -/
def affineChartPsiPullback {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d)).obj
      ((Modules.restrictToScheme (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
        ((Modules.pullback (ofOverMap (relativeProjToZ (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg))).obj
          ((Modules.pullback (affineOpenHom g U)).obj (deg.obj n)))) ⟶
    (Scheme.Modules.pullback (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d)).obj
      ((Modules.restrictToScheme (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
        ((Modules.pullback (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj
          (obj F hF n))) :=
  (Scheme.Modules.pullback (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d)).map
    (psi_pullback_restrict (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF n)

/-- Identify pullback of the affine-model twisting sheaf along the composite
classifying section with pullback along `affineChartSection`. -/
def affineChartTargetIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback
        (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d ≫
          schemeSectionMap (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U)) n) ≅
    (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U))
        n) :=
  (Scheme.Modules.pullbackCongr (affineChartSectionMap_comp g F hF U d)).app
    (Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U)) n)

/-- Target of the chart restriction of the pullback of `ψ`. -/
abbrev affineChartPsiTarget {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :=
  (Scheme.Modules.pullback (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d)).obj
    ((Modules.restrictToScheme (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj
        (obj F hF n)))

/-- Target of the canonical affine chart formula `affineChartPsiModel`. -/
abbrev affineChartModelTarget {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :=
  (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
    (Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U)) n)

/-- Classifying-section pullback of the affine-model twisting sheaf on
`underline{Proj}_U(g^* 𝒜|_U)`. -/
abbrev affineChartPUSerreTarget {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (n : ℕ) :=
  (Scheme.Modules.pullback (schemeSectionMap (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj
    (Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U)) n)

/-- The affine-model twisting sheaf remains quasi-coherent after pullback along
the classifying section of `underline{Proj}_U(g^* 𝒜|_U)`. -/
theorem affineChartPUSerreTarget_isQuasicoherent {Z : Over S}
    (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (n : ℕ) :
    (affineChartPUSerreTarget g F hF U n).IsQuasicoherent :=
  sorry

section AffineScheme
variable {T Z : Over S} (g : ofOver Z ⟶ X) (q : ofOver T ⟶ X)
variable (t : T ⟶ Z) (ht : ofOverMap t ≫ g = q) (F : ProjFunctor X 𝒜)
variable [hA : (pullbackAlgebra g deg).IsCommutative]
variable [hB : (pullbackAlgebra q deg).IsCommutative]

/-- Homogeneous modules compare by the actual composite pullback isomorphism. -/
private def affineSchemeDegreePullIso (n : ℕ) :
    (Scheme.Modules.pullback t.left).obj (pullbackAlgebra g deg (n : ℤ)) ≅
      pullbackAlgebra q deg (n : ℤ) :=
  @Modules.RestrictToScheme.compositePullbackIso S X T Z g t (deg.obj n)
      (deg.isQuasicoherent F.algebra_isQuasicoherent n) ≪≫
    (Modules.restrictToScheme T).mapIso
      (eqToIso (congrArg (fun a ↦ (Modules.pullback a).obj (deg.obj n)) ht))

/-- Homogeneous sections pull back and then pass through the composite comparison. -/
private def affineSchemeDegreeSectionsMap (n : ℕ) :
    RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra g deg) n →+
      RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra q deg) n :=
  AddMonoidHom.comp
    (show Scheme.Modules.globalSections
        ((Scheme.Modules.pullback t.left).obj (pullbackAlgebra g deg (n : ℤ))) →+
        RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra q deg) n from
      (Scheme.Modules.globalSectionsMap (affineSchemeDegreePullIso (deg := deg) g q t ht F n).hom).hom)
    (show RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra g deg) n →+
        Scheme.Modules.globalSections
          ((Scheme.Modules.pullback t.left).obj (pullbackAlgebra g deg (n : ℤ))) from
      (Scheme.Modules.globalSectionsPullback t.left (pullbackAlgebra g deg (n : ℤ))).hom)

/-- The componentwise additive map of the actual affine section rings. -/
private def affineSchemeAddMap :
    Scheme.RelativeProjAffineSectionRing.ring (pullbackAlgebra g deg) →+
      Scheme.RelativeProjAffineSectionRing.ring (pullbackAlgebra q deg) :=
  Scheme.RelativeProjAffineSectionRing.SectionMap.addMap
    (pullbackAlgebra g deg) (pullbackAlgebra q deg)
    (affineSchemeDegreeSectionsMap (deg := deg) g q t ht F)

/-- Homogeneous generators map to the inclusions of their pulled-back sections. -/
private theorem affineSchemeAddMap_of (n : ℕ)
    (x : RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra g deg) n) :
    affineSchemeAddMap (deg := deg) g q t ht F
        (DirectSum.of (RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra g deg)) n x) =
      DirectSum.of (RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra q deg)) n
        (affineSchemeDegreeSectionsMap (deg := deg) g q t ht F n x) :=
  Scheme.RelativeProjAffineSectionRing.SectionMap.addMap_of
    (pullbackAlgebra g deg) (pullbackAlgebra q deg)
    (affineSchemeDegreeSectionsMap (deg := deg) g q t ht F) n x

/-- The actual scalar-extension map preserves the unit section. -/
private theorem affineSchemeAddMap_one : affineSchemeAddMap (deg := deg) g q t ht F 1 = 1 := sorry

/-- The actual scalar-extension map preserves products of section-ring elements. -/
private theorem affineSchemeAddMap_mul (x y) :
    affineSchemeAddMap (deg := deg) g q t ht F (x * y) =
      affineSchemeAddMap (deg := deg) g q t ht F x * affineSchemeAddMap (deg := deg) g q t ht F y := sorry

/-- The actual componentwise section map with its ring laws. -/
private def affineSchemeRingMap :
    Scheme.RelativeProjAffineSectionRing.ring (pullbackAlgebra g deg) →+*
      Scheme.RelativeProjAffineSectionRing.ring (pullbackAlgebra q deg) :=
  Scheme.RelativeProjAffineSectionRing.SectionMap.ringMap
    (pullbackAlgebra g deg) (pullbackAlgebra q deg)
    (affineSchemeDegreeSectionsMap (deg := deg) g q t ht F)
    (affineSchemeAddMap_one (deg := deg) g q t ht F) (affineSchemeAddMap_mul (deg := deg) g q t ht F)

/-- The ring map has the specified value on every homogeneous generator. -/
private theorem affineSchemeRingMap_of (n : ℕ)
    (x : RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra g deg) n) :
    affineSchemeRingMap (deg := deg) g q t ht F
        (DirectSum.of (RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra g deg)) n x) =
      DirectSum.of (RingedSpace.GradedAlgebraSections.degree (pullbackAlgebra q deg)) n
        (affineSchemeDegreeSectionsMap (deg := deg) g q t ht F n x) :=
  Scheme.RelativeProjAffineSectionRing.SectionMap.ringMap_of
    (pullbackAlgebra g deg) (pullbackAlgebra q deg)
    (affineSchemeDegreeSectionsMap (deg := deg) g q t ht F)
    (affineSchemeAddMap_one (deg := deg) g q t ht F) (affineSchemeAddMap_mul (deg := deg) g q t ht F) n x

/-- The scalar-extension ring map preserves homogeneous summands. -/
private theorem affineSchemeGradedMap_mem (n : ℕ) (x)
    (hx : x ∈ Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg) n) :
    affineSchemeRingMap (deg := deg) g q t ht F x ∈
      Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra q deg) n :=
  Scheme.RelativeProjAffineSectionRing.SectionMap.ringMap_mem
    (pullbackAlgebra g deg) (pullbackAlgebra q deg)
    (affineSchemeDegreeSectionsMap (deg := deg) g q t ht F)
    (affineSchemeAddMap_one (deg := deg) g q t ht F) (affineSchemeAddMap_mul (deg := deg) g q t ht F) n x hx

/-- The scalar-extension map between the actual graded section rings. -/
private def affineSchemeGradedMap :
    Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg) →+*ᵍ
      Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra q deg) :=
  Scheme.RelativeProjAffineSectionRing.SectionMap.gradedMap
    (pullbackAlgebra g deg) (pullbackAlgebra q deg)
    (affineSchemeDegreeSectionsMap (deg := deg) g q t ht F)
    (affineSchemeAddMap_one (deg := deg) g q t ht F) (affineSchemeAddMap_mul (deg := deg) g q t ht F)

/-- Affine scalar extension has full projective domain without a flatness assumption. -/
private theorem affineSchemeGradedMap_domain [IsAffine Z.left] [IsAffine T.left] :
    projMapDomain (affineSchemeGradedMap (deg := deg) g q t ht F) = ⊤ := sorry

/-- The actual projective map induced by affine scalar extension. -/
private def affineSchemeProjMap [IsAffine Z.left] [IsAffine T.left] :
    Scheme.RelativeProjAffineSectionRing.scheme (pullbackAlgebra q deg) ⟶
      Scheme.RelativeProjAffineSectionRing.scheme (pullbackAlgebra g deg) :=
  Scheme.RelativeProjAffineSectionRing.SectionMap.projMap
    (pullbackAlgebra g deg) (pullbackAlgebra q deg)
    (affineSchemeGradedMap (deg := deg) g q t ht F) (affineSchemeGradedMap_domain (deg := deg) g q t ht F)

/-- The fraction-induced comparison of twists for the actual affine scalar extension. -/
private def affineSchemeSerreHom [IsAffine Z.left] [IsAffine T.left] (n : ℤ) :
    (Scheme.Modules.pullback (affineSchemeProjMap (deg := deg) g q t ht F)).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg)) n) ⟶
    Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra q deg)) n :=
  Scheme.RelativeProjAffineSectionRing.SectionMap.twistHom
    (pullbackAlgebra g deg) (pullbackAlgebra q deg)
    (affineSchemeGradedMap (deg := deg) g q t ht F) (affineSchemeGradedMap_domain (deg := deg) g q t ht F) n

/-- Sectionwise preimages of the fraction comparison, with zero fallback, define its inverse. -/
private def affineSchemeSerreInv [IsAffine Z.left] [IsAffine T.left] (n : ℤ) :
    Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra q deg)) n ⟶
    (Scheme.Modules.pullback (affineSchemeProjMap (deg := deg) g q t ht F)).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg)) n) := by
  let A : (Scheme.RelativeProjAffineSectionRing.scheme (pullbackAlgebra q deg)).Modules :=
    (Scheme.Modules.pullback (affineSchemeProjMap (deg := deg) g q t ht F)).obj
    (Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg)) n)
  let B : (Scheme.RelativeProjAffineSectionRing.scheme (pullbackAlgebra q deg)).Modules :=
    Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra q deg)) n
  let f : A ⟶ B := affineSchemeSerreHom (deg := deg) g q t ht F n
  let inv := fun V ↦ Modules.RestrictToScheme.preimageOr 0 (fun x ↦ (f.val.app V).hom x)
  have laws :
      (∀ V (x y : B.val.obj V), inv V (x + y) = inv V x + inv V y) ∧
      (∀ V (r : (Scheme.RelativeProjAffineSectionRing.scheme (pullbackAlgebra q deg)).ringCatSheaf.obj.obj V)
        (x : B.val.obj V), inv V (r • x) = r • inv V x) ∧
      (∀ {V W} (i : V ⟶ W) (x : B.val.obj V),
        A.val.map i (inv V x) = inv W (B.val.map i x)) := by sorry
  exact { val := {
    app := fun V ↦ ModuleCat.ofHom {
      toFun := inv V
      map_add' := laws.1 V
      map_smul' := laws.2.1 V }
    naturality := by intro V W i; ext x; exact (laws.2.2 i x).symm } }

/-- The actual fraction map and its specified inverse identify affine pullback twists. -/
private def affineSchemeSerreIso [IsAffine Z.left] [IsAffine T.left] (n : ℤ) :
    (Scheme.Modules.pullback (affineSchemeProjMap (deg := deg) g q t ht F)).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg)) n) ≅
    Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra q deg)) n := by
  let hom := affineSchemeSerreHom (deg := deg) g q t ht F n
  let inv := affineSchemeSerreInv (deg := deg) g q t ht F n
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := by sorry
  exact ⟨hom, inv, laws.1, laws.2⟩

end AffineScheme

/-- The graph test determines its actual leg to the affine étale chart. -/
private def affineChartGraphMap {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W) : W.obj.left ⟶ V.obj.left :=
  yoneda.preimage (j.left ≫ etaleBaseChangeSnd (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj)

/-- The structural leg of an affine graph test maps to the affine base open. -/
private def affineChartGraphBase {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg))) : W.obj.left ⟶ affineOpenOver U :=
  yoneda.preimage W.obj.hom ≫
    relativeProjToZ (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg

/-- The two legs of a graph test have the same morphism to the original base. -/
private theorem affineChartGraph_base {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W) :
    (ofOverMap (affineChartGraphMap g F hF U V W j) ≫ base F hF V = ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF)) ∧
    (ofOverMap (affineChartGraphBase g F hF U W) ≫ affineOpenHom g U = ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF)) := sorry

/-- The actual represented graph-test point classifies a section-algebra Proj point. -/
private def affineChartGraphClassifyingMap {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    [hW : (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg).IsCommutative] :
    W.obj.left.left ⟶ Scheme.RelativeProjAffineSectionRing.scheme
      (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg) := by
  let r : ofOver W.obj.left ⟶ toAlgebraicSpace F hF := W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF
  let x : F.toFunctor.obj (op W.obj.left) := r.app (op W.obj.left) (𝟙 W.obj.left)
  let q := hF.quadrupleOf W.obj.left x
  have hq : q.morphism = ofOverMap (𝟙 W.obj.left) ≫ (r ≫ toAlgebraicSpace_hom F hF) := by
    apply yonedaEquiv.injective
    change q.morphism.app (op W.obj.left) (𝟙 W.obj.left) =
      F.baseMap.app (op W.obj.left)
        (r.app (op W.obj.left) ((𝟙 W.obj.left) ≫ (𝟙 W.obj.left)))
    simpa only [Category.id_comp] using
      hF.base_eq W.obj.left x q (hF.associated_quadrupleOf W.obj.left x)
  exact (Scheme.RelativeProjAffineSectionRing.degreeAssociated
      (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg)
      (pullbackAlgebra_isQuasicoherent ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg F.algebra_isQuasicoherent) q.positive).pointOf
        W.obj.left.left
        (RelativeProjBaseChangeData.toSchemeQuadruple ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg
          F.algebra_isQuasicoherent (𝟙 W.obj.left) q hq) ≫
    (Proj.degreeOpen (Scheme.RelativeProjAffineSectionRing.grading
      (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg)) q.degree).ι

/-- The common Serre twist is the pullback along the actual graph-test classifying point. -/
private def affineChartGraphCommonTwist {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    [hW : (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg).IsCommutative] (n : ℤ) :
    W.obj.left.left.Modules :=
  (Scheme.Modules.pullback (affineChartGraphClassifyingMap g F hF U W)).obj
    (Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg)) n)

/-- The graph leg respects the classifying maps and affine scalar extension. -/
private theorem affineChartGraph_classifying_graph {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W)
    [hW : (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg).IsCommutative] :
    affineChartGraphClassifyingMap g F hF U W ≫
        affineSchemeProjMap (deg := deg) (hA := localAlgebra_commutative F hF V) (base F hF V) ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF)
          (affineChartGraphMap g F hF U V W j) (affineChartGraph_base g F hF U V W j).1 F =
      (affineChartGraphMap g F hF U V W j).left ≫ sectionMap F hF V := sorry

/-- The structural leg respects the classifying maps and affine scalar extension. -/
private theorem affineChartGraph_classifying_base {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W)
    [hU : (affineOpenAlgebra g deg U).IsCommutative]
    [hW : (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg).IsCommutative] :
    affineChartGraphClassifyingMap g F hF U W ≫
        affineSchemeProjMap (deg := deg) (affineOpenHom g U) ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF)
          (affineChartGraphBase g F hF U W) (affineChartGraph_base g F hF U V W j).2 F =
      (yoneda.preimage W.obj.hom).left ≫
        schemeSectionMap (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF := sorry

/-- Pullback of the local affine Serre sheaf maps into the common graph-test twist. -/
private def affineChartGraphSerreForward {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W)
    [hW : (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg).IsCommutative] (n : ℤ) :
    (Scheme.Modules.pullback (affineChartGraphMap g F hF U V W j).left).obj
      (localObj F hF V n) ⟶ affineChartGraphCommonTwist g F hF U W n :=
  (Scheme.Modules.pullbackComp (affineChartGraphMap g F hF U V W j).left
      (sectionMap F hF V)).hom.app _ ≫
    (Scheme.Modules.pullbackCongr (affineChartGraph_classifying_graph g F hF U V W j)).inv.app _ ≫
    (Scheme.Modules.pullbackComp (affineChartGraphClassifyingMap g F hF U W)
      (affineSchemeProjMap (deg := deg) (hA := localAlgebra_commutative F hF V) (base F hF V) ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF)
        (affineChartGraphMap g F hF U V W j) (affineChartGraph_base g F hF U V W j).1 F)).inv.app _ ≫
    (Scheme.Modules.pullback (affineChartGraphClassifyingMap g F hF U W)).map
      (affineSchemeSerreHom (deg := deg) (hA := localAlgebra_commutative F hF V) (base F hF V) ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF)
        (affineChartGraphMap g F hF U V W j) (affineChartGraph_base g F hF U V W j).1 F n)

/-- The inverse structural scalar comparison maps the common twist to the model pullback. -/
private def affineChartGraphSerreBackward {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W)
    [hU : (affineOpenAlgebra g deg U).IsCommutative]
    [hW : (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg).IsCommutative] (n : ℕ) :
    affineChartGraphCommonTwist g F hF U W n ⟶
      (Scheme.Modules.pullback (yoneda.preimage W.obj.hom).left).obj
        (affineChartPUSerreTarget g F hF U n) :=
  (Scheme.Modules.pullback (affineChartGraphClassifyingMap g F hF U W)).map
      (affineSchemeSerreIso (deg := deg) (affineOpenHom g U) ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF)
        (affineChartGraphBase g F hF U W) (affineChartGraph_base g F hF U V W j).2 F n).inv ≫
    (Scheme.Modules.pullbackComp (affineChartGraphClassifyingMap g F hF U W)
      (affineSchemeProjMap (deg := deg) (affineOpenHom g U) ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF)
        (affineChartGraphBase g F hF U W) (affineChartGraph_base g F hF U V W j).2 F)).hom.app _ ≫
    (Scheme.Modules.pullbackCongr (affineChartGraph_classifying_base g F hF U V W j)).hom.app _ ≫
    (Scheme.Modules.pullbackComp (yoneda.preimage W.obj.hom).left
      (schemeSectionMap (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).inv.app _

/-- The graph comparison is the composite of the two specified Serre comparisons. -/
private def affineChartGraphSerreHom {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W)
    [hU : (affineOpenAlgebra g deg U).IsCommutative]
    [hW : (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg).IsCommutative] (n : ℕ) :
    (Scheme.Modules.pullback (affineChartGraphMap g F hF U V W j).left).obj
      (localObj F hF V n) ⟶
      (Scheme.Modules.pullback (yoneda.preimage W.obj.hom).left).obj
        (affineChartPUSerreTarget g F hF U n) :=
  affineChartGraphSerreForward g F hF U V W j n ≫
    affineChartGraphSerreBackward g F hF U V W j n

/-- The local affine comparison is pulled back on actual global sections. -/
private def affineChartGraphPulledSection {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W) (n : ℕ)
    (x : (obj F hF n).val.obj (op V.obj)) :
    Scheme.Modules.globalSections
      ((Scheme.Modules.pullback (affineChartGraphMap g F hF U V W j).left).obj
        (localObj F hF V n)) :=
  (Scheme.Modules.globalSectionsPullback (affineChartGraphMap g F hF U V W j).left
    (localObj F hF V n)).hom
      (((affineComparison F hF n).inv.val.app (op V)).hom x)

/-- Applying the local Serre comparison gives the actual affine-model section. -/
private def affineChartGraphModelSection {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W)
    [hU : (affineOpenAlgebra g deg U).IsCommutative]
    [hW : (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg).IsCommutative] (n : ℕ)
    (x : (obj F hF n).val.obj (op V.obj)) :
    Scheme.Modules.globalSections
      ((Scheme.Modules.pullback (yoneda.preimage W.obj.hom).left).obj
        (affineChartPUSerreTarget g F hF U n)) :=
  (Scheme.Modules.globalSectionsMap (affineChartGraphSerreHom g F hF U V W j n)).hom
    (affineChartGraphPulledSection g F hF U V W j n x)

/-- Extension and pullback transport the actual model section to its étale chart. -/
private def affineChartGraphSection {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    (V : affineEtaleSite (toAlgebraicSpace F hF))
    (W : affineEtaleSite (ofOver (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)))
    (j : AffineGraph (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) V.obj W)
    [hU : (affineOpenAlgebra g deg U).IsCommutative]
    [hW : (pullbackAlgebra ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg).IsCommutative] (n : ℕ)
    (x : (obj F hF n).val.obj (op V.obj)) :
    ((Modules.RestrictToScheme.extension (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
      (affineChartPUSerreTarget g F hF U n)).val.obj (op W.obj) := by
  let Q := relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg
  let M : Q.left.Modules := affineChartPUSerreTarget g F hF U n
  let N : (ofOver Q).Modules := (Modules.RestrictToScheme.extension Q).obj M
  let w : W.obj.left ⟶ Q := yoneda.preimage W.obj.hom
  let A := (Scheme.Modules.pullback w.left).obj M
  let y : Scheme.Modules.globalSections A := affineChartGraphModelSection g F hF U V W j n x
  let forward : A ⟶ (Modules.restrictToScheme W.obj.left).obj
      ((Modules.pullback W.obj.hom).obj N) :=
    (Modules.RestrictToScheme.extensionAdjunction W.obj.left).unit.app A ≫
      (Modules.restrictToScheme W.obj.left).map
        ((Modules.RestrictToScheme.extensionPullbackIso w).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (Modules.pullback a).obj N)
            (yoneda.map_preimage W.obj.hom)))
  let z := (Modules.RestrictToScheme.sectionEquiv W.obj.left
    ((Modules.pullback W.obj.hom).obj N) ⊤)
      ((Scheme.Modules.globalSectionsMap forward).hom y)
  let a := ((@Modules.restrictFunctorIsoPullback _ _ _ W.obj.hom
      (etale_hom W.obj)).inv.app N).val.app
        (op (Modules.RestrictToScheme.siteObject W.obj.left ⊤))
  let z' := (@Modules.restrictAppIso _ _ _ N W.obj.hom (etale_hom W.obj)
    (Modules.RestrictToScheme.siteObject W.obj.left ⊤)).hom (a z)
  let topIso : (Modules.restrictPostcompose W.obj.hom).obj
      (Modules.RestrictToScheme.siteObject W.obj.left ⊤) ≅ W.obj :=
    MorphismProperty.CostructuredArrow.isoMk
      (Over.isoMk (Scheme.topIso W.obj.left.left) rfl) trivial trivial (by
        rfl)
  exact N.val.map topIso.inv.op z'

/-- The specified graph-test values form the affine matching family for the direct image. -/
private def affineChartGraphMatching {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hU : (affineOpenAlgebra g deg U).IsCommutative]
    (V : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ)
    (x : (obj F hF n).val.obj (op V.obj)) :
    AffineMatching (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)
      ((Modules.RestrictToScheme.extension (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
        (affineChartPUSerreTarget g F hF U n)) V.obj where
  value W j := affineChartGraphSection g F hF U V W j
    (hW := @pullbackAlgebra_isCommutative S X 𝒜 W.obj.left ((W.obj.hom ≫ toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) ≫ toAlgebraicSpace_hom F hF) deg F.algebra_isCommutative) n x
  compatible := sorry

/-- Matching-family reconstruction gives the specified morphism on the affine basis. -/
private def affineChartBasisDirectMap {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hU : (affineOpenAlgebra g deg U).IsCommutative] (n : ℕ) :
    ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj (obj F hF n) ⟶
    ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
      ((Modules.pushforward (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj
        ((Modules.RestrictToScheme.extension (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
          (affineChartPUSerreTarget g F hF U n))) := by
  let P := toAlgebraicSpace F hF
  let N := (Modules.RestrictToScheme.extension (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
    (affineChartPUSerreTarget g F hF U n)
  let A : SheafOfModules.{u} (affineStructureSheaf P) :=
    ((affineInclusionRingedHom P).modulePushforward).obj (obj F hF n)
  let B : SheafOfModules.{u} (affineStructureSheaf P) :=
    ((affineInclusionRingedHom P).modulePushforward).obj
    ((Modules.pushforward (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj N)
  let f : ∀ V : (affineEtaleSite P)ᵒᵖ, A.val.obj V → B.val.obj V := fun V x ↦
    sectionOfMatching (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF) N V.unop.obj (affineChartGraphMatching g F hF U V.unop n x)
  have laws :
      (∀ V (x y : A.val.obj V), f V (x + y) = f V x + f V y) ∧
      (∀ V (r : (affineStructureSheaf P).obj.obj V) (x : A.val.obj V),
        f V (r • x) = r • f V x) ∧
      (∀ {V W} (i : V ⟶ W) (x : A.val.obj V),
        B.val.map i (f V x) = f W (A.val.map i x)) := by sorry
  exact { val := {
    app := fun V ↦ @ModuleCat.ofHom ((affineStructureSheaf P).obj.obj V) _
      (A.val.obj V) (B.val.obj V)
      (A.val.obj V).isAddCommGroup (A.val.obj V).isModule
      (B.val.obj V).isAddCommGroup (B.val.obj V).isModule {
      toFun := f V
      map_add' := laws.1 V
      map_smul' := laws.2.1 V }
    naturality := by intro V W i; ext x; exact (laws.2.2 i x).symm } }

/-- Fullness of dense-basis restriction descends the specified basis morphism. -/
private def affineChartDirectMap {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hU : (affineOpenAlgebra g deg U).IsCommutative] (n : ℕ) :
    obj F hF n ⟶ (Modules.pushforward (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj
      ((Modules.RestrictToScheme.extension (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
        (affineChartPUSerreTarget g F hF U n)) :=
  ((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).preimage
    (affineChartBasisDirectMap g F hF U n)

/-- The canonical comparison is the adjoint of the descended matching-family map. -/
@[no_expose] def affineChartPUSerreHom {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hU : (affineOpenAlgebra g deg U).IsCommutative] (n : ℕ) :
    (Modules.restrictToScheme (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj (obj F hF n)) ⟶
    affineChartPUSerreTarget g F hF U n := by
  exact (Modules.restrictToScheme (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).map
      (((Modules.pullbackPushforwardAdjunction (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).homEquiv _ _).symm
        (affineChartDirectMap g F hF U n)) ≫
    (@Modules.RestrictToScheme.unitIso S (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)
      (affineChartPUSerreTarget g F hF U n)
      (affineChartPUSerreTarget_isQuasicoherent g F hF U n)).inv

/-- Sectionwise preimages of the canonical comparison give its specified inverse. -/
def affineChartPUSerreInv {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hU : (affineOpenAlgebra g deg U).IsCommutative] (n : ℕ) :
    affineChartPUSerreTarget g F hF U n ⟶
    (Modules.restrictToScheme (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj (obj F hF n)) := by
  let A : (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg).left.Modules := (Modules.restrictToScheme (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
    ((Modules.pullback (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj (obj F hF n))
  let B : (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg).left.Modules := affineChartPUSerreTarget g F hF U n
  let f : A ⟶ B := affineChartPUSerreHom g F hF U n
  let inv := fun V ↦ Modules.RestrictToScheme.preimageOr 0 (fun x ↦ (f.val.app V).hom x)
  have laws :
      (∀ V (x y : B.val.obj V), inv V (x + y) = inv V x + inv V y) ∧
      (∀ V (r : (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg).left.ringCatSheaf.obj.obj V) (x : B.val.obj V),
        inv V (r • x) = r • inv V x) ∧
      (∀ {V W} (i : V ⟶ W) (x : B.val.obj V),
        A.val.map i (inv V x) = inv W (B.val.map i x)) := by sorry
  exact { val := {
    app := fun V ↦ @ModuleCat.ofHom ((relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg).left.ringCatSheaf.obj.obj V) _
      (B.val.obj V) (A.val.obj V)
      (B.val.obj V).isAddCommGroup (B.val.obj V).isModule
      (A.val.obj V).isAddCommGroup (A.val.obj V).isModule {
      toFun := inv V
      map_add' := laws.1 V
      map_smul' := laws.2.1 V }
    naturality := by intro V W i; ext x; exact (laws.2.2 i x).symm } }

/-- The specified canonical comparison and inverse identify the two pullback twists. -/
def affineChartPUSerreIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hU : (affineOpenAlgebra g deg U).IsCommutative] (n : ℕ) :
    (Modules.restrictToScheme (relativeProjOver (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).obj (obj F hF n)) ≅
    affineChartPUSerreTarget g F hF U n := by
  let hom := affineChartPUSerreHom g F hF U n
  let inv := affineChartPUSerreInv g F hF U n
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := by sorry
  exact ⟨hom, inv, laws.1, laws.2⟩

/-- Canonical identification of the restricted pullback of `𝒪_P(n)` with the
affine-model twisting sheaf on a positive-degree chart: descent of `obj` to the
classifying-section pullback of `twistingSheaf`, transported along
`AlgebraicGeometry.RelativeProjFunctor.degreeMap`, then `pullbackCongr` of `affineChartSectionMap_comp`. -/
def affineChartTwistIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    affineChartPsiTarget g F hF U d n ≅ affineChartModelTarget g F hF U d n :=
  (Scheme.Modules.pullback (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d)).mapIso
      (affineChartPUSerreIso g F hF U n) ≪≫
    (Scheme.Modules.pullbackComp
        (AlgebraicGeometry.RelativeProjFunctor.degreeMap (F := (affineOpenProj g deg F U)) d)
        (schemeSectionMap (F_Z := affineOpenProj g deg F U) (affineOpenHom g U) F hF)).app
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U))
        n) ≪≫
    affineChartTargetIso g F hF U d n

/-- The named composite of source transport, chart restriction of `ψ`, and
`affineChartTwistIso`, landing on the affine-model Serre twist. -/
def affineChartPsiComparison {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase (affineOpenAlgebra g deg U))).obj
        ((affineOpenAlgebra g deg U).obj (n : ℤ))) ⟶
    (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U))
        n) :=
  (affineChartSourceIso g F hF U d n).hom ≫
    affineChartPsiSourceComparison g F hF U d n ≫
      affineChartPsiPullback g F hF U d n ≫
        (affineChartTwistIso g F hF U d n).hom

/-- The canonical affine scheme chart formula of `g^* 𝒜|_U`: pull
`homogeneousPullbackMap` back along the classifying section of a positive-degree
chart. -/
def affineChartPsiModel {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [hA : (affineOpenAlgebra g deg U).IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase (affineOpenAlgebra g deg U))).obj
        ((affineOpenAlgebra g deg U).obj (n : ℤ))) ⟶
    (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U))
        n) :=
  (Scheme.Modules.pullback (affineChartSection g F hF U d)).map
    (Scheme.RelativeProjAffineSectionRing.homogeneousPullbackMap
      (affineOpenAlgebra g deg U) (affineOpenAlgebra_isQuasicoherent g deg F U) n)


end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- The canonical homomorphism agrees with the scheme construction after every scheme base change. -/
theorem psi_baseChange {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) {Z : Over S} (g : ofOver Z ⟶ X)
    (U : Z.left.affineOpens) (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    CanonicalTwists.affineChartPsiComparison g F hF U
        (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg F U) d n =
      CanonicalTwists.affineChartPsiModel g F hF U
        (hA := CanonicalTwists.affineOpenAlgebra_isCommutative g deg F U) d n := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
