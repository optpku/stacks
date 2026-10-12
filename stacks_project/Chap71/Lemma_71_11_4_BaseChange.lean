/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_11_4_Psi
public import stacks_project.Chap71.Lemma_71_11_2

/-!
# Scheme-level base change of the canonical homomorphism `ψ`

For a scheme `Z` over `X`, the isomorphism of Lemma 71.11.2 identifies
`underline{Proj}_Z(g^* 𝒜)` with the fibre product `Z ×_X P`. Pullback of `ψ`
along the second projection is the space-level form of the nonnegative twist
map of Constructions Lemma 27.15.5.
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
    pullbackOverSnd g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal

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

/-- `psi_baseChange_hom` is the module pullback of `psi.hom n`. -/
theorem psi_baseChange_hom_eq {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (n : ℕ) :
    psi_baseChange_hom g F hF n =
      (Modules.pullback (toRelativeProj g F hF)).map ((psi F hF).hom n) :=
  sorry

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

/-- `psi_pullback` is `psi.hom n` after the fibre-product identifications. -/
theorem psi_pullback_eq {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (n : ℕ) :
    psi_pullback g F hF n =
      (Modules.pullbackCompIso (ofOverMap (relativeProjToZ g deg)) g).hom.app (deg.obj n) ≫
        eqToHom (congrArg (fun f ↦ (Modules.pullback f).obj (deg.obj n))
          (toRelativeProj_comp g F hF).symm) ≫
        (Modules.pullbackCompIso (toRelativeProj g F hF)
            (toAlgebraicSpace_hom F hF)).inv.app (deg.obj n) ≫
          psi_baseChange_hom g F hF n :=
  sorry

/-- Commutativity of `g^* 𝒜`, recorded from the relative Proj owner. -/
theorem pullbackAlgebra_isCommutative_of {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) :
    (pullbackAlgebra g deg).IsCommutative :=
  sorry

/-- The Constructions Lemma 27.15.5 affine chart map of `g^* 𝒜`: the homogeneous
pullback map of the affine section algebra of `pullbackAlgebra g deg`. -/
def schemeChartPsi {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    [𝒜.IsCommutative] [IsAffine Z.left] (n : ℕ) :
    (Scheme.Modules.pullback
      (Scheme.RelativeProjAffineSectionRing.toBase (pullbackAlgebra g deg))).obj
      ((pullbackAlgebra g deg).obj (n : ℤ)) ⟶
    Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg)) (n : ℤ) :=
  Scheme.RelativeProjAffineSectionRing.homogeneousPullbackMap
    (pullbackAlgebra g deg)
    (pullbackAlgebra_isQuasicoherent g deg F.algebra_isQuasicoherent) n

/-- `schemeChartPsi` is `homogeneousPullbackMap` of `pullbackAlgebra g deg`. -/
theorem schemeChartPsi_eq {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    [𝒜.IsCommutative] [IsAffine Z.left] (n : ℕ) :
    schemeChartPsi g F n =
      Scheme.RelativeProjAffineSectionRing.homogeneousPullbackMap
        (pullbackAlgebra g deg)
        (pullbackAlgebra_isQuasicoherent g deg F.algebra_isQuasicoherent) n :=
  sorry

/-- The classifying map of a positive-degree chart of `underline{Proj}_Z(g^* 𝒜)`
into the affine section-algebra Proj. -/
def degreeChartSection {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [𝒜.IsCommutative] [IsAffine Z.left] (d : { n : ℕ // 1 ≤ n }) :
    degreeChartScheme g deg d ⟶
      Scheme.RelativeProjAffineSectionRing.scheme (pullbackAlgebra g deg) :=
  (Scheme.RelativeProjAffineSectionRing.degreeAssociated (pullbackAlgebra g deg)
      (pullbackAlgebra_isQuasicoherent g deg F.algebra_isQuasicoherent) d.2).pointOf
      (degreeChartScheme g deg d)
      (RelativeProjBaseChangeData.universalChartQuadruple g deg d) ≫
    (Proj.degreeOpen
      (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg)) d.1).ι

/-- `degreeChartSection` classifies the universal chart quadruple in the affine model. -/
theorem degreeChartSection_eq {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [𝒜.IsCommutative] [IsAffine Z.left] (d : { n : ℕ // 1 ≤ n }) :
    degreeChartSection g F d =
      (Scheme.RelativeProjAffineSectionRing.degreeAssociated (pullbackAlgebra g deg)
          (pullbackAlgebra_isQuasicoherent g deg F.algebra_isQuasicoherent) d.2).pointOf
          (degreeChartScheme g deg d)
          (RelativeProjBaseChangeData.universalChartQuadruple g deg d) ≫
        (Proj.degreeOpen
          (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg))
          d.1).ι :=
  sorry

/-- Degree-chart classifying maps agree on overlaps, so they glue over `P_Z`. -/
theorem degreeChartSection_compatible {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [𝒜.IsCommutative] [IsAffine Z.left] :
    ∀ d e : { n : ℕ // 1 ≤ n },
      pullback.fst (degreeChartImmersion g deg d) (degreeChartImmersion g deg e) ≫
          degreeChartSection g F d =
        pullback.snd (degreeChartImmersion g deg d) (degreeChartImmersion g deg e) ≫
          degreeChartSection g F e :=
  sorry

/-- The classifying section `underline{Proj}_Z(g^* 𝒜) ⟶ Proj(Γ(Z, g^* 𝒜))` of the
affine 27.15.5 model. -/
def schemeSectionMap {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [𝒜.IsCommutative] [IsAffine Z.left] :
    F_Z.toFunctor.reprX ⟶
      Scheme.RelativeProjAffineSectionRing.scheme (pullbackAlgebra g deg) :=
  Scheme.Cover.glueMorphisms (relativeProjDegreeCover g deg)
    (degreeChartSection g F) (degreeChartSection_compatible g F)

/-- The classifying section lies over `π_Z`. -/
theorem schemeSectionMap_toBase {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [𝒜.IsCommutative] [IsAffine Z.left] :
    schemeSectionMap g F hF ≫
        Scheme.RelativeProjAffineSectionRing.toBase (pullbackAlgebra g deg) =
      relativeProjToZLeft g deg :=
  sorry

/-- The 27.15.5 chart formula on `P_Z`: pull `homogeneousPullbackMap` back along
the classifying section. -/
def schemeLocalPsi {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [𝒜.IsCommutative] [IsAffine Z.left] (n : ℕ) :
    (Scheme.Modules.pullback (schemeSectionMap g F hF)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase (pullbackAlgebra g deg))).obj
        ((pullbackAlgebra g deg).obj (n : ℤ))) ⟶
    (Scheme.Modules.pullback (schemeSectionMap g F hF)).obj
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (pullbackAlgebra g deg))
        (n : ℤ)) :=
  (Scheme.Modules.pullback (schemeSectionMap g F hF)).map (schemeChartPsi g F n)

/-- `schemeLocalPsi` is the pullback of `schemeChartPsi` along `schemeSectionMap`. -/
theorem schemeLocalPsi_eq {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [𝒜.IsCommutative] [IsAffine Z.left] (n : ℕ) :
    schemeLocalPsi g F hF n =
      (Scheme.Modules.pullback (schemeSectionMap g F hF)).map (schemeChartPsi g F n) :=
  sorry

/-- Identify the iterated pullback along `schemeSectionMap` and `toBase` with pullback
along `π_Z`, using `schemeSectionMap_toBase`. -/
def schemeLocalPsiSourceIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [𝒜.IsCommutative] [IsAffine Z.left] (n : ℕ) :
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

/-- `schemeLocalPsiSourceIso` is `pullbackComp` followed by `pullbackCongr` of
`schemeSectionMap_toBase`. -/
theorem schemeLocalPsiSourceIso_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    [𝒜.IsCommutative] [IsAffine Z.left] (n : ℕ) :
    schemeLocalPsiSourceIso g F hF n =
      (Scheme.Modules.pullbackComp (schemeSectionMap g F hF)
          (Scheme.RelativeProjAffineSectionRing.toBase (pullbackAlgebra g deg))).app
        ((pullbackAlgebra g deg).obj (n : ℤ)) ≪≫
      (Scheme.Modules.pullbackCongr (schemeSectionMap_toBase g F hF)).app
        ((pullbackAlgebra g deg).obj (n : ℤ)) :=
  sorry

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

/-- `schemePsiSourceComparison` is `pullbackComparison` after the nonnegative-degree
identification of `pullbackAlgebra`. -/
theorem schemePsiSourceComparison_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (n : ℕ) :
    schemePsiSourceComparison g F hF n =
      eqToHom (congrArg
          (fun M ↦ (Scheme.Modules.pullback (relativeProjToZLeft g deg)).obj M)
          (pullbackAlgebra_obj_ofNat g deg n)) ≫
        Modules.RestrictToScheme.pullbackComparison (relativeProjToZ g deg)
          ((Modules.pullback g).obj (deg.obj n)) :=
  sorry

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

/-- `psi_pullback_restrict` is scheme-restriction of `psi_pullback`. -/
theorem psi_pullback_restrict_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    [F_Z : AlgebraicGeometry.RelativeProjFunctor Z.left (pullbackAlgebra g deg)]
    (n : ℕ) :
    psi_pullback_restrict g F hF n =
      (Modules.restrictToScheme (relativeProjOver g deg)).map
        (psi_pullback g F hF n) :=
  sorry

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

/-- `affineOpenAlgebra` is `pullbackAlgebra` of the restricted morphism `U ⟶ X`. -/
theorem affineOpenAlgebra_eq {Z : Over S} (g : ofOver Z ⟶ X) (deg : DegreePieces 𝒜)
    (U : Z.left.affineOpens) :
    affineOpenAlgebra g deg U = pullbackAlgebra (affineOpenHom g U) deg :=
  sorry

/-- Quasi-coherence of the affine-open restriction. -/
theorem affineOpenAlgebra_isQuasicoherent {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (F : ProjFunctor X 𝒜) (U : Z.left.affineOpens) :
    (affineOpenAlgebra g deg U).IsQuasicoherent :=
  pullbackAlgebra_isQuasicoherent (affineOpenHom g U) deg F.algebra_isQuasicoherent

/-- Commutativity of the affine-open restriction, from the source algebra. -/
instance affineOpenAlgebra_isCommutative {Z : Over S} (g : ofOver Z ⟶ X)
    (deg : DegreePieces 𝒜) (U : Z.left.affineOpens) [𝒜.IsCommutative] :
    (affineOpenAlgebra g deg U).IsCommutative :=
  pullbackAlgebra_isCommutative (affineOpenHom g U) deg

/-- The classifying section of a positive-degree chart of
`underline{Proj}_U(g^* 𝒜|_U)` into the affine 27.15.5 model `Proj Γ(U, g^* 𝒜)`. -/
def affineChartSection {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) :
    degreeChartScheme (affineOpenHom g U) deg d ⟶
      Scheme.RelativeProjAffineSectionRing.scheme (affineOpenAlgebra g deg U) :=
  degreeChartSection (affineOpenHom g U) F d

/-- `affineChartSection` is the affine-open specialization of `degreeChartSection`. -/
theorem affineChartSection_eq {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) :
    affineChartSection g F hF U d = degreeChartSection (affineOpenHom g U) F d :=
  sorry

/-- The classifying section of the chart lies over `U`. -/
theorem affineChartSection_toBase {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) :
    affineChartSection g F hF U d ≫
        Scheme.RelativeProjAffineSectionRing.toBase (affineOpenAlgebra g deg U) =
      degreeChartToBase (affineOpenHom g U) deg d :=
  sorry

/-- A positive-degree chart of `underline{Proj}_U(g^* 𝒜|_U)` lies over `U`. -/
theorem affineChartImmersion_toBase {Z : Over S} (g : ofOver Z ⟶ X)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    (d : { n : ℕ // 1 ≤ n }) :
    degreeChartImmersion (affineOpenHom g U) deg d ≫
        relativeProjToZLeft (affineOpenHom g U) deg =
      degreeChartToBase (affineOpenHom g U) deg d :=
  sorry

/-- The glued classifying section restricts to `affineChartSection` on a
positive-degree chart. -/
theorem affineChartSectionMap_comp {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) :
    degreeChartImmersion (affineOpenHom g U) deg d ≫
        schemeSectionMap (affineOpenHom g U) F hF =
      affineChartSection g F hF U d :=
  sorry

/-- Quasi-coherence of the canonical twist. -/
theorem obj_isQuasicoherent (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (n : ℕ) :
    (obj F hF n).IsQuasicoherent :=
  sorry

/-- Source comparison of the 27.15.5 chart formula: iterated pullback along the
classifying section and `toBase` identifies with pullback along the chart
structure map to `U`. -/
def affineChartSourceIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase (affineOpenAlgebra g deg U))).obj
        ((affineOpenAlgebra g deg U).obj (n : ℤ))) ≅
    (Scheme.Modules.pullback (degreeChartToBase (affineOpenHom g U) deg d)).obj
      ((affineOpenAlgebra g deg U).obj (n : ℤ)) :=
  (Scheme.Modules.pullbackComp (affineChartSection g F hF U d)
      (Scheme.RelativeProjAffineSectionRing.toBase (affineOpenAlgebra g deg U))).app
    ((affineOpenAlgebra g deg U).obj (n : ℤ)) ≪≫
  (Scheme.Modules.pullbackCongr (affineChartSection_toBase g F hF U d)).app
    ((affineOpenAlgebra g deg U).obj (n : ℤ))

/-- `affineChartSourceIso` is `pullbackComp` followed by `pullbackCongr` of
`affineChartSection_toBase`. -/
theorem affineChartSourceIso_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    affineChartSourceIso g F hF U d n =
      (Scheme.Modules.pullbackComp (affineChartSection g F hF U d)
          (Scheme.RelativeProjAffineSectionRing.toBase (affineOpenAlgebra g deg U))).app
        ((affineOpenAlgebra g deg U).obj (n : ℤ)) ≪≫
      (Scheme.Modules.pullbackCongr (affineChartSection_toBase g F hF U d)).app
        ((affineOpenAlgebra g deg U).obj (n : ℤ)) :=
  sorry

/-- Source transport from `π_U^* (g^* 𝒜_n)` on a positive-degree chart to the
algebraic-space pullback source of `psi_pullback`. -/
def affineChartPsiSourceComparison {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback (degreeChartToBase (affineOpenHom g U) deg d)).obj
      ((affineOpenAlgebra g deg U).obj (n : ℤ)) ⟶
    (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).obj
      ((Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
        ((Modules.pullback (ofOverMap (relativeProjToZ (affineOpenHom g U) deg))).obj
          ((Modules.pullback (affineOpenHom g U)).obj (deg.obj n)))) :=
  (Scheme.Modules.pullbackCongr (affineChartImmersion_toBase g U d)).inv.app
    ((affineOpenAlgebra g deg U).obj (n : ℤ)) ≫
  (Scheme.Modules.pullbackComp (degreeChartImmersion (affineOpenHom g U) deg d)
      (relativeProjToZLeft (affineOpenHom g U) deg)).inv.app
    ((affineOpenAlgebra g deg U).obj (n : ℤ)) ≫
  (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).map
    (schemePsiSourceComparison (affineOpenHom g U) F hF n)

/-- Restriction of `psi_pullback` to a positive-degree chart of
`underline{Proj}_U(g^* 𝒜|_U)`. -/
def affineChartPsiPullback {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).obj
      ((Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
        ((Modules.pullback (ofOverMap (relativeProjToZ (affineOpenHom g U) deg))).obj
          ((Modules.pullback (affineOpenHom g U)).obj (deg.obj n)))) ⟶
    (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).obj
      ((Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
        ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
          (obj F hF n))) :=
  (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).map
    (psi_pullback_restrict (affineOpenHom g U) F hF n)

/-- `affineChartPsiPullback` is pullback of `psi_pullback_restrict` along the chart. -/
theorem affineChartPsiPullback_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    affineChartPsiPullback g F hF U d n =
      (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).map
        (psi_pullback_restrict (affineOpenHom g U) F hF n) :=
  sorry

/-- Identify pullback of the affine-model twisting sheaf along the composite
classifying section with pullback along `affineChartSection`. -/
def affineChartTargetIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    (Scheme.Modules.pullback
        (degreeChartImmersion (affineOpenHom g U) deg d ≫
          schemeSectionMap (affineOpenHom g U) F hF)).obj
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
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :=
  (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).obj
    ((Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
        (obj F hF n)))

/-- Target of the 27.15.5 chart formula `affineChartPsiModel`. -/
abbrev affineChartModelTarget {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :=
  (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
    (Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U)) n)

/-- Base change of the dense-basis counit of `obj` along `toRelativeProj`. -/
def affineChartPUObjCounit {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    (n : ℕ) :
    (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
        ((affineExtension (toAlgebraicSpace F hF)).obj
          (((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
            (obj F hF n)))) ⟶
    (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
        (obj F hF n)) :=
  (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).map
    ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).map
      ((affineExtensionAdjunction (toAlgebraicSpace F hF)).counit.app (obj F hF n)))

/-- The dense-basis counit remains invertible after pullback to `P_U`. -/
instance affineChartPUObjCounit_isIso {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    (n : ℕ) :
    IsIso (affineChartPUObjCounit g F hF U n) := sorry

/-- The inverse of the pulled-back dense-basis counit of `obj`. -/
def affineChartPUObjCounitInv {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    (n : ℕ) :
    (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
        (obj F hF n)) ⟶
    (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
        ((affineExtension (toAlgebraicSpace F hF)).obj
          (((affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
            (obj F hF n)))) :=
  @CategoryTheory.inv _ _ _ _
    (affineChartPUObjCounit g F hF U n)
    (affineChartPUObjCounit_isIso g F hF U n)

/-- Classifying-section pullback of the affine-model twisting sheaf on
`underline{Proj}_U(g^* 𝒜|_U)`. -/
abbrev affineChartPUSerreTarget {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :=
  (Scheme.Modules.pullback (schemeSectionMap (affineOpenHom g U) F hF)).obj
    (Proj.AssociatedModule.twistingSheaf
      (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U)) n)

/-- `affineChartPUSerreTarget` is the classifying-section pullback of
`twistingSheaf`. -/
theorem affineChartPUSerreTarget_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    affineChartPUSerreTarget g F hF U n =
      (Scheme.Modules.pullback (schemeSectionMap (affineOpenHom g U) F hF)).obj
        (Proj.AssociatedModule.twistingSheaf
          (Scheme.RelativeProjAffineSectionRing.grading
            (affineOpenAlgebra g deg U)) n) :=
  sorry

/-- The affine-model twisting sheaf remains quasi-coherent after pullback along
the classifying section of `underline{Proj}_U(g^* 𝒜|_U)`. -/
instance affineChartPUSerreTarget_isQuasicoherent {Z : Over S}
    (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    (affineChartPUSerreTarget g F hF U n).IsQuasicoherent :=
  sorry

/-- On `underline{Proj}_U(g^* 𝒜|_U)`, the pullback of `𝒪_P(n)` is the extension of
the classifying-section pullback of `twistingSheaf`. -/
theorem affineChartPUSerreSpace_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    (Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj (obj F hF n) =
      (Modules.RestrictToScheme.extension
        (relativeProjOver (affineOpenHom g U) deg)).obj
        (affineChartPUSerreTarget g F hF U n) :=
  sorry

/-- The extension/restriction unit at the classifying-section pullback of
`twistingSheaf`. -/
def affineChartPUSerreUnit {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    affineChartPUSerreTarget g F hF U n ⟶
      (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
        ((Modules.RestrictToScheme.extension
          (relativeProjOver (affineOpenHom g U) deg)).obj
          (affineChartPUSerreTarget g F hF U n)) :=
  (Modules.RestrictToScheme.extensionAdjunction
    (relativeProjOver (affineOpenHom g U) deg)).unit.app
    (affineChartPUSerreTarget g F hF U n)

/-- `affineChartPUSerreUnit` is the extension/restriction unit. -/
theorem affineChartPUSerreUnit_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    affineChartPUSerreUnit g F hF U n =
      (Modules.RestrictToScheme.extensionAdjunction
        (relativeProjOver (affineOpenHom g U) deg)).unit.app
        (affineChartPUSerreTarget g F hF U n) :=
  sorry

/-- The extension/restriction unit is invertible on the quasi-coherent
classifying-section pullback of `twistingSheaf`. -/
instance affineChartPUSerreUnit_isIso {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    IsIso (affineChartPUSerreUnit g F hF U n) :=
  sorry

/-- Inverse of the extension/restriction unit at the classifying-section
pullback of `twistingSheaf`. -/
def affineChartPUSerreUnitIso {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    affineChartPUSerreTarget g F hF U n ≅
      (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
        ((Modules.RestrictToScheme.extension
          (relativeProjOver (affineOpenHom g U) deg)).obj
          (affineChartPUSerreTarget g F hF U n)) :=
  @asIso _ _ _ _ (affineChartPUSerreUnit g F hF U n)
    (affineChartPUSerreUnit_isIso g F hF U n)

/-- The P_U-level comparison morphism from the restricted pullback of `𝒪_P(n)`
to the classifying-section pullback of `twistingSheaf`. The underlying map is
restriction of `eqToHom` of `affineChartPUSerreSpace_eq`, followed by the inverse
of the extension/restriction unit. -/
def affineChartPUSerreHom {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
        (obj F hF n)) ⟶
    affineChartPUSerreTarget g F hF U n :=
  (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).map
      (eqToHom (affineChartPUSerreSpace_eq g F hF U n)) ≫
    (affineChartPUSerreUnitIso g F hF U n).inv

/-- The inverse P_U-level Serre comparison. -/
def affineChartPUSerreInv {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    affineChartPUSerreTarget g F hF U n ⟶
      (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
        ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
          (obj F hF n)) :=
  (affineChartPUSerreUnitIso g F hF U n).hom ≫
    (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).map
      (eqToHom (affineChartPUSerreSpace_eq g F hF U n).symm)

/-- Descent comparison of the pulled-back global twist `𝒪_P(n)` with the
classifying-section pullback of `Proj.AssociatedModule.twistingSheaf`. The
forward map is restriction of `eqToHom` of `affineChartPUSerreSpace_eq`
followed by the inverse extension/restriction unit. -/
def affineChartPUSerreIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
      ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
        (obj F hF n)) ≅
    affineChartPUSerreTarget g F hF U n :=
  (Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).mapIso
      (eqToIso (affineChartPUSerreSpace_eq g F hF U n)) ≪≫
    (affineChartPUSerreUnitIso g F hF U n).symm

/-- `affineChartPUSerreIso.hom` is restriction of the space identification
followed by the inverse extension/restriction unit. -/
theorem affineChartPUSerreIso_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (n : ℕ) :
    (affineChartPUSerreIso g F hF U n).hom =
      affineChartPUSerreHom g F hF U n :=
  sorry

/-- Canonical identification of the restricted pullback of `𝒪_P(n)` with the
affine-model twisting sheaf on a positive-degree chart: descent of `obj` to the
classifying-section pullback of `twistingSheaf`, transported along
`degreeChartImmersion`, then `pullbackCongr` of `affineChartSectionMap_comp`. -/
def affineChartTwistIso {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    affineChartPsiTarget g F hF U d n ≅ affineChartModelTarget g F hF U d n :=
  (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).mapIso
      (affineChartPUSerreIso g F hF U n) ≪≫
    (Scheme.Modules.pullbackComp
        (degreeChartImmersion (affineOpenHom g U) deg d)
        (schemeSectionMap (affineOpenHom g U) F hF)).app
      (Proj.AssociatedModule.twistingSheaf
        (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U))
        n) ≪≫
    affineChartTargetIso g F hF U d n

/-- `affineChartTwistIso` is descent of `obj`, transported along the chart
immersion and composed with `affineChartTargetIso`. -/
theorem affineChartTwistIso_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    affineChartTwistIso g F hF U d n =
      (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).mapIso
          (affineChartPUSerreIso g F hF U n) ≪≫
        (Scheme.Modules.pullbackComp
            (degreeChartImmersion (affineOpenHom g U) deg d)
            (schemeSectionMap (affineOpenHom g U) F hF)).app
          (Proj.AssociatedModule.twistingSheaf
            (Scheme.RelativeProjAffineSectionRing.grading
              (affineOpenAlgebra g deg U)) n) ≪≫
        affineChartTargetIso g F hF U d n :=
  sorry

/-- The named composite of source transport, chart restriction of `ψ`, and
`affineChartTwistIso`, landing on the affine-model Serre twist. -/
def affineChartPsiComparison {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
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

/-- `affineChartPsiComparison` is the source/target transport of the chart
restriction of `ψ`. -/
theorem affineChartPsiComparison_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    affineChartPsiComparison g F hF U d n =
      (affineChartSourceIso g F hF U d n).hom ≫
        affineChartPsiSourceComparison g F hF U d n ≫
          affineChartPsiPullback g F hF U d n ≫
            (affineChartTwistIso g F hF U d n).hom :=
  sorry

/-- The Constructions Lemma 27.15.5 chart formula of `g^* 𝒜|_U`: pull
`homogeneousPullbackMap` back along the classifying section of a positive-degree
chart. -/
def affineChartPsiModel {Z : Over S} (g : ofOver Z ⟶ X) (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
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

/-- `affineChartPsiModel` is the pullback of `homogeneousPullbackMap` along
`affineChartSection`. -/
theorem affineChartPsiModel_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    affineChartPsiModel g F hF U d n =
      (Scheme.Modules.pullback (affineChartSection g F hF U d)).map
        (Scheme.RelativeProjAffineSectionRing.homogeneousPullbackMap
          (affineOpenAlgebra g deg U)
          (affineOpenAlgebra_isQuasicoherent g deg F U) n) :=
  sorry

/-- `affineChartPsiTarget` is the chart pullback of the restricted global twist. -/
theorem affineChartPsiTarget_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    affineChartPsiTarget g F hF U d n =
      (Scheme.Modules.pullback (degreeChartImmersion (affineOpenHom g U) deg d)).obj
        ((Modules.restrictToScheme (relativeProjOver (affineOpenHom g U) deg)).obj
          ((Modules.pullback (toRelativeProj (affineOpenHom g U) F hF)).obj
            (obj F hF n))) :=
  sorry

/-- `affineChartModelTarget` is the pullback of the affine-model twisting sheaf. -/
theorem affineChartModelTarget_eq {Z : Over S} (g : ofOver Z ⟶ X)
    (F : ProjFunctor X 𝒜) (hF : F.IsAssociatedToQuadruples deg)
    (U : Z.left.affineOpens)
    [F_U : AlgebraicGeometry.RelativeProjFunctor (affineOpenOver U).left
      (affineOpenAlgebra g deg U)]
    [𝒜.IsCommutative] (d : { n : ℕ // 1 ≤ n }) (n : ℕ) :
    affineChartModelTarget g F hF U d n =
      (Scheme.Modules.pullback (affineChartSection g F hF U d)).obj
        (Proj.AssociatedModule.twistingSheaf
          (Scheme.RelativeProjAffineSectionRing.grading (affineOpenAlgebra g deg U))
          n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists
