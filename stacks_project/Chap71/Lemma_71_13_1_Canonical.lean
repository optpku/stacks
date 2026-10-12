/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap65.Lemma_65_11_3_OfRepresentable
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap71.Lemma_71_11_5_TwistPushforward
public import stacks_project.Chap71.Lemma_71_13_1_SectionMap

/-!
# Canonical open, morphism, and twist comparison of a relative Proj section map

The open `U(ψ)` is the fppf subfunctor of tests on which some positive-degree component of
`ψ` is an epimorphism. The morphism `r_{L,ψ}` classifies the restricted quadruple, and `θ`
is the adjoint of the descended direct-image map assembled from affine matching families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : X ⟶ Y)
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y)}
variable (deg : DegreePieces 𝒜) {F : ProjFunctor Y 𝒜}
variable (hF : F.IsAssociatedToQuadruples deg) (L : X.Modules)
variable [isInvertibleObject L] (ψ : GradedMapToPowers f deg L)

/-- The restriction of `ψ` to a test morphism `w : T ⟶ X`, in degree `d`. -/
def restrictedDegreeMap {T : Over S} (w : ofOver T ⟶ X) (d : ℕ) :
    (Modules.pullback (w ≫ f)).obj (deg.obj d) ⟶
      tensorPowerUnit ((Modules.pullback w).obj L) d :=
  (Modules.pullbackCompIso w f).inv.app (deg.obj d) ≫
    (Modules.pullback w).map (ψ.hom d) ≫ pullbackTensorPowerHom w L d

/-- `restrictedDegreeMap` is composite-pullback comparison, then `ψ`, then the
tensor-power comparison. -/
theorem restrictedDegreeMap_eq {T : Over S} (w : ofOver T ⟶ X) (d : ℕ) :
    restrictedDegreeMap f deg L ψ w d =
      (Modules.pullbackCompIso w f).inv.app (deg.obj d) ≫
        (Modules.pullback w).map (ψ.hom d) ≫ pullbackTensorPowerHom w L d :=
  sorry

/-- Homogeneous components of the Veronese restriction of `ψ` along `w`, rebracketed as
maps into tensor powers of `L^{⊗ d}|_T`. -/
def restrictedPsi {T : Over S} (w : ofOver T ⟶ X) (d n : ℕ) :
    (Modules.pullback (w ≫ f)).obj (deg.obj (n * d)) ⟶
      tensorPowerUnit (tensorPowerUnit ((Modules.pullback w).obj L) d) n :=
  (Modules.pullbackCompIso w f).inv.app (deg.obj (n * d)) ≫
    (Modules.pullback w).map (ψ.hom (n * d)) ≫
      pullbackTensorPowerHom w L (n * d) ≫
        (tensorPowerUnitMulIso ((Modules.pullback w).obj L) d n).hom

/-- `restrictedPsi` is the degree-`(n * d)` component of `ψ`, rebracketed as a tensor power
of `L^{⊗ d}`. -/
theorem restrictedPsi_eq {T : Over S} (w : ofOver T ⟶ X) (d n : ℕ) :
    restrictedPsi f deg L ψ w d n =
      (Modules.pullbackCompIso w f).inv.app (deg.obj (n * d)) ≫
        (Modules.pullback w).map (ψ.hom (n * d)) ≫
          pullbackTensorPowerHom w L (n * d) ≫
            (tensorPowerUnitMulIso ((Modules.pullback w).obj L) d n).hom :=
  sorry

/-- The relative projective quadruple `(d, T ⟶ Y, L^{⊗ d}|_T, ψ^{(d)}|_T)` on a test where
the degree-`d` map is an epimorphism. -/
def restrictedQuadruple {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    Quadruple 𝒜 deg T :=
  Quadruple.of d hd (w ≫ f)
    (tensorPowerUnit ((Modules.pullback w).obj L) d) sorry
    (restrictedPsi f deg L ψ w d) sorry sorry
    (restrictedPsi f deg L ψ w d 1) sorry sorry

/-- The structure morphism of `restrictedQuadruple` is `w ≫ f`. -/
theorem restrictedQuadruple_morphism {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    (restrictedQuadruple f deg L ψ w d hd hEpi).morphism = w ≫ f :=
  rfl

/-- The line bundle of `restrictedQuadruple` is `L^{⊗ d}|_T`. -/
theorem restrictedQuadruple_lineBundle {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    (restrictedQuadruple f deg L ψ w d hd hEpi).lineBundle =
      tensorPowerUnit ((Modules.pullback w).obj L) d :=
  rfl

/-- A quasi-compact test morphism to `X` lies in `U(ψ)` when some positive-degree component
of `ψ` is an epimorphism. -/
def memDomainQc {T : Over S} [CompactSpace T.left] (w : ofOver T ⟶ X) : Prop :=
  ∃ d : ℕ, 1 ≤ d ∧ Epi (restrictedDegreeMap f deg L ψ w d)

/-- A general test morphism to `X` lies in `U(ψ)` when every quasi-compact open restriction
does. -/
def memDomain {T : Over S} (w : ofOver T ⟶ X) : Prop :=
  ∀ (V : T.left.Opens) [CompactSpace V.toScheme],
    memDomainQc f deg L ψ (ofOverMap (openOverι T V) ≫ w)

/-- On a quasi-compact test, membership in `U(ψ)` is existence of a positive-degree
epimorphism. -/
theorem memDomain_iff_exists_epi {T : Over S} [CompactSpace T.left]
    (w : ofOver T ⟶ X) :
    memDomain f deg L ψ w ↔
      ∃ d : ℕ, 1 ≤ d ∧ Epi (restrictedDegreeMap f deg L ψ w d) :=
  sorry

/-- A globally epimorphic positive-degree restriction lies in `U(ψ)`. -/
theorem memDomain_of_epi {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    memDomain f deg L ψ w :=
  sorry

/-- The fppf subfunctor of `X` classified by `memDomain`. -/
def domainSubfunctor : Subfunctor X.functorOfPoints where
  obj T := {t | memDomain f deg L ψ (pointHom t)}
  map := sorry

/-- The inclusion of `domainSubfunctor` is relatively representable. -/
theorem domain_relativelyRepresentable :
    yoneda.relativelyRepresentable (domainSubfunctor f deg L ψ).ι :=
  sorry

/-- The algebraic space underlying `U(ψ)`, obtained from the relatively representable
subfunctor of surjective-degree tests. -/
def domainSpace : AlgebraicSpace S :=
  ofRelativelyRepresentable (domainSubfunctor f deg L ψ).ι
    (domain_relativelyRepresentable f deg L ψ)

/-- The open subspace `U(ψ) ⊂ X`. -/
def domain : OpenSubspace X where
  X := domainSpace f deg L ψ
  ι := ofRelativelyRepresentable_hom (domainSubfunctor f deg L ψ).ι
      (domain_relativelyRepresentable f deg L ψ)
  isOpenImmersion := sorry

/-- The inclusion of `domain` is the subfunctor inclusion. -/
theorem domain_ι_eq :
    (domain f deg L ψ).ι =
      ofRelativelyRepresentable_hom (domainSubfunctor f deg L ψ).ι
        (domain_relativelyRepresentable f deg L ψ) :=
  sorry

/-- The functor of points of `domain` is the subfunctor of surjective-degree tests. -/
theorem domain_functorOfPoints :
    (domain f deg L ψ).X.functorOfPoints =
      (domainSubfunctor f deg L ψ).toFunctor :=
  rfl

/-- A chosen positive degree witnessing that a quasi-compact test lies in `U(ψ)`. -/
def chosenDegree {T : Over S} [CompactSpace T.left] {w : ofOver T ⟶ X}
    (hw : memDomainQc f deg L ψ w) : ℕ :=
  Classical.choose hw

/-- The chosen degree is at least one. -/
theorem chosenDegree_pos {T : Over S} [CompactSpace T.left] {w : ofOver T ⟶ X}
    (hw : memDomainQc f deg L ψ w) :
    1 ≤ chosenDegree f deg L ψ hw :=
  (Classical.choose_spec hw).1

/-- The restricted degree map in the chosen degree is an epimorphism. -/
theorem chosenDegree_epi {T : Over S} [CompactSpace T.left] {w : ofOver T ⟶ X}
    (hw : memDomainQc f deg L ψ w) :
    Epi (restrictedDegreeMap f deg L ψ w (chosenDegree f deg L ψ hw)) :=
  (Classical.choose_spec hw).2

/-- The classifying point of a quasi-compact `U(ψ)`-test, via the restricted quadruple. -/
def canonicalPointQc (T : Over S) [CompactSpace T.left]
    (x : {t : X.functorOfPoints.obj (op T) // memDomainQc f deg L ψ (pointHom t)}) :
    F.toFunctor.obj (op T) :=
  hF.pointOf T
    (restrictedQuadruple f deg L ψ (pointHom x.1)
      (chosenDegree f deg L ψ x.2)
      (chosenDegree_pos f deg L ψ x.2)
      (chosenDegree_epi f deg L ψ x.2))

/-- The classifying point of a general `U(ψ)`-test, glued from quasi-compact opens. -/
def canonicalPoint (T : Over S)
    (x : {t : X.functorOfPoints.obj (op T) // memDomain f deg L ψ (pointHom t)}) :
    F.toFunctor.obj (op T) :=
  (hF.qcLimit T).symm
    (ProjFunctor.QcCompatibleSystem.of
      (fun V _ ↦
        canonicalPointQc f deg hF L ψ (openOver T V)
          ⟨X.functorOfPoints.map (op (openOverι T V)) x.1, sorry⟩)
      sorry)

/-- `canonicalPointQc` is `pointOf` of the restricted quadruple. -/
theorem canonicalPointQc_eq (T : Over S) [CompactSpace T.left]
    (x : {t : X.functorOfPoints.obj (op T) // memDomainQc f deg L ψ (pointHom t)}) :
    canonicalPointQc f deg hF L ψ T x =
      hF.pointOf T
        (restrictedQuadruple f deg L ψ (pointHom x.1)
          (chosenDegree f deg L ψ x.2)
          (chosenDegree_pos f deg L ψ x.2)
          (chosenDegree_epi f deg L ψ x.2)) :=
  sorry

/-- The morphism `r_{L,ψ} : U(ψ) ⟶ underline{Proj}_Y(𝒜)`, as a natural transformation of
functors of points. -/
def canonicalMap : (domain f deg L ψ).X ⟶ toAlgebraicSpace F hF where
  app T :=
    TypeCat.ofHom fun
      (x : (domainSubfunctor f deg L ψ).toFunctor.obj T) ↦
        canonicalPoint f deg hF L ψ T.unop ⟨x.1, x.2⟩
  naturality := sorry

/-- The canonical morphism `r_{L,ψ}` lies over `Y`. -/
theorem canonicalMap_over_base :
    canonicalMap f deg hF L ψ ≫ toAlgebraicSpace_hom F hF =
      (domain f deg L ψ).ι ≫ f :=
  sorry

/-- The adjoint of `ψ` in degree `d`, as a map `𝒜_d ⟶ f_* L^{⊗ d}`. -/
def psiPushforward (d : ℕ) :
    deg.obj d ⟶ (Modules.pushforward f).obj (tensorPowerUnit L d) :=
  ((Modules.pullbackPushforwardAdjunction f).homEquiv
      (deg.obj d) (tensorPowerUnit L d)) (ψ.hom d)

/-- Restriction of `f_* L^{⊗ d}` along `U(ψ) ⊂ X`. -/
def restrictPushforward (d : ℕ) :
    (Modules.pushforward f).obj (tensorPowerUnit L d) ⟶
      (Modules.pushforward ((domain f deg L ψ).ι ≫ f)).obj
        ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d)) :=
  (Modules.pushforward f).map
      ((Modules.pullbackPushforwardAdjunction (domain f deg L ψ).ι).unit.app
        (tensorPowerUnit L d)) ≫
    (Modules.pushforwardComp (domain f deg L ψ).ι f).hom.app
      ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d))

/-- Local algebra-to-twist map on an affine étale chart: pull back
`homogeneousPullbackMap` along the classifying section. -/
def chartLocalPsi (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    (Scheme.Modules.pullback (CanonicalTwists.sectionMap F hF U)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase
          (CanonicalTwists.localAlgebra F hF U))).obj
        (CanonicalTwists.localAlgebra F hF U (n : ℤ))) ⟶
    CanonicalTwists.localObj F hF U n :=
  (Scheme.Modules.pullback (CanonicalTwists.sectionMap F hF U)).map
    (Scheme.RelativeProjAffineSectionRing.homogeneousPullbackMap
      (CanonicalTwists.localAlgebra F hF U)
      (CanonicalTwists.localAlgebra_quasicoherent F hF U) n)

/-- Identify the iterated pullback of the local algebra along `sectionMap` and
`toBase` with the local algebra itself. -/
def chartLocalPsiSourceIso
    (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    (Scheme.Modules.pullback (CanonicalTwists.sectionMap F hF U)).obj
      ((Scheme.Modules.pullback
        (Scheme.RelativeProjAffineSectionRing.toBase
          (CanonicalTwists.localAlgebra F hF U))).obj
        (CanonicalTwists.localAlgebra F hF U (n : ℤ))) ≅
    CanonicalTwists.localAlgebra F hF U (n : ℤ) :=
  (Scheme.Modules.pullbackComp (CanonicalTwists.sectionMap F hF U)
      (Scheme.RelativeProjAffineSectionRing.toBase
        (CanonicalTwists.localAlgebra F hF U))).app
    (CanonicalTwists.localAlgebra F hF U (n : ℤ)) ≪≫
  (Scheme.Modules.pullbackCongr (CanonicalTwists.sectionMap_toBase F hF U)).app
    (CanonicalTwists.localAlgebra F hF U (n : ℤ)) ≪≫
  (Scheme.Modules.pullbackId U.obj.left.left).app
    (CanonicalTwists.localAlgebra F hF U (n : ℤ))

/-- Chartwise nonnegative comparison `localAlgebra_n ⟶ localObj_n`. -/
def chartAlgebraToTwist
    (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    CanonicalTwists.localAlgebra F hF U (n : ℤ) ⟶
      CanonicalTwists.localObj F hF U n :=
  (chartLocalPsiSourceIso deg hF U n).inv ≫ chartLocalPsi deg hF U n

/-- `chartAlgebraToTwist` is `chartLocalPsi` after the classifying-section
identification. -/
theorem chartAlgebraToTwist_eq
    (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    chartAlgebraToTwist deg hF U n =
      (chartLocalPsiSourceIso deg hF U n).inv ≫ chartLocalPsi deg hF U n :=
  sorry

/-- Restriction of `π^* 𝒜_n` to the affine étale basis. -/
def affinePullbackSheaf (n : ℕ) :
    SheafOfModules.{u}
      (affineStructureSheaf (toAlgebraicSpace F hF)) :=
  ((CanonicalTwists.affineInclusionRingedHom (toAlgebraicSpace F hF)).modulePushforward).obj
    ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n))

/-- Local-algebra global sections, with the affine-basis structure-ring action. -/
def chartAffineSourceModule
    (U : affineEtaleSite (toAlgebraicSpace F hF)) (n : ℕ) :
    ModuleCat.{u}
      ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.obj (op U)) :=
  (ModuleCat.restrictScalars
    (eqToIso (affineStructureSheaf_obj U)).hom.hom).obj
      (U.obj.left.left.toRingedSpace.moduleGlobalSectionsFunctor.obj
        (CanonicalTwists.localAlgebra F hF U (n : ℤ)))

/-- The identity-on-underlying-scheme comparison from the top-open étale object of an
affine chart to the chart itself. -/
def affineChartFromSiteObject
    (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) :
    (Modules.restrictPostcompose U.unop.obj.hom).obj
      (Modules.RestrictToScheme.siteObject U.unop.obj.left ⊤) ⟶
    U.unop.obj :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (⊤ : U.unop.obj.left.left.Opens).ι sorry) trivial sorry

/-- Sections of the affine-basis pullback sheaf are sections of `π^* 𝒜_n` on the
underlying small étale object. -/
def affinePullbackAsEtale
    (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (n : ℕ)
    (x : (affinePullbackSheaf deg hF n).val.obj U) :
    ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)).val.obj
      (op U.unop.obj) :=
  x

/-- Identify `π^* 𝒜_n` on an affine chart with the restricted composite pullback,
evaluated at the top open. -/
def affinePullbackToSourceApp
    (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (n : ℕ) :
    (affinePullbackSheaf deg hF n).val.obj U ⟶
      (ModuleCat.restrictScalars
        (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
          (((Modules.restrictToScheme U.unop.obj.left).obj
            ((Modules.pullback U.unop.obj.hom).obj
              ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
                (deg.obj n)))).val.obj (op ⊤)) :=
  @ModuleCat.ofHom
    ((affineStructureSheaf (toAlgebraicSpace F hF)).obj.obj U) _
    ((affinePullbackSheaf deg hF n).val.obj U)
    ((ModuleCat.restrictScalars
      (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
        (((Modules.restrictToScheme U.unop.obj.left).obj
          ((Modules.pullback U.unop.obj.hom).obj
            ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
              (deg.obj n)))).val.obj (op ⊤)))
    ((affinePullbackSheaf deg hF n).val.obj U).isAddCommGroup
    ((affinePullbackSheaf deg hF n).val.obj U).isModule
    ((ModuleCat.restrictScalars
      (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
        (((Modules.restrictToScheme U.unop.obj.left).obj
          ((Modules.pullback U.unop.obj.hom).obj
            ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
              (deg.obj n)))).val.obj (op ⊤))).isAddCommGroup
    ((ModuleCat.restrictScalars
      (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
        (((Modules.restrictToScheme U.unop.obj.left).obj
          ((Modules.pullback U.unop.obj.hom).obj
            ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
              (deg.obj n)))).val.obj (op ⊤))).isModule
    { toFun := fun x ↦
        (Modules.RestrictToScheme.sectionEquiv U.unop.obj.left
            ((Modules.pullback U.unop.obj.hom).obj
              ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)))
            ⊤).symm
          (((@Modules.restrictFunctorIsoPullback _ _ _ U.unop.obj.hom
                (etale_hom U.unop.obj)).app
              ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n))).hom.val.app
            (op (Modules.RestrictToScheme.siteObject U.unop.obj.left ⊤))
            ((@Modules.restrictAppIso _ _ _
                ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n))
                U.unop.obj.hom (etale_hom U.unop.obj)
                (Modules.RestrictToScheme.siteObject U.unop.obj.left ⊤)).inv
              (((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)).val.map
                (affineChartFromSiteObject deg hF U).op
                (affinePullbackAsEtale deg hF U n x))))
      map_add' := sorry
      map_smul' := sorry }

/-- Transport restricted composite-pullback sections to local-algebra sections. -/
def restrictTopToLocalAlgebra
    (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (n : ℕ) :
    (ModuleCat.restrictScalars
        (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).obj
      (((Modules.restrictToScheme U.unop.obj.left).obj
        ((Modules.pullback U.unop.obj.hom).obj
          ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
            (deg.obj n)))).val.obj (op ⊤)) ⟶
      chartAffineSourceModule deg hF U.unop n :=
  (ModuleCat.restrictScalars
      (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).map
    ((((Modules.restrictToScheme U.unop.obj.left).mapIso
        ((Modules.pullbackCompIso U.unop.obj.hom
            (toAlgebraicSpace_hom F hF)).app (deg.obj n))).hom.val.app (op ⊤)))

/-- Chartwise `chartAlgebraToTwist` as a map of affine-basis modules. -/
def chartAffinePsiApp
    (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (n : ℕ) :
    chartAffineSourceModule deg hF U.unop n ⟶
      CanonicalTwists.affineSectionModule F hF U.unop (n : ℤ) :=
  (ModuleCat.restrictScalars
      (eqToIso (affineStructureSheaf_obj U.unop)).hom.hom).map
    (U.unop.obj.left.left.toRingedSpace.moduleGlobalSectionsFunctor.map
      (chartAlgebraToTwist deg hF U.unop n))

/-- Chartwise `chartAlgebraToTwist` on restricted `π^* 𝒜_n` sections. -/
def affinePullbackPsiApp
    (U : (affineEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (n : ℕ) :
    (affinePullbackSheaf deg hF n).val.obj U ⟶
      CanonicalTwists.affineSectionModule F hF U.unop (n : ℤ) :=
  affinePullbackToSourceApp deg hF U n ≫
    restrictTopToLocalAlgebra deg hF U n ≫
      chartAffinePsiApp deg hF U n

/-- Affine-basis morphism whose extension is the degree-`n` algebra-to-twist map. -/
def affinePsiMap (n : ℕ) :
    affinePullbackSheaf deg hF n ⟶ CanonicalTwists.affineSheaf F hF (n : ℤ) where
  val :=
    { app := fun U ↦ affinePullbackPsiApp deg hF U n
      naturality := sorry }

/-- The inverse of the dense-basis counit, obtained by fullness from the unit. -/
def moduleAffineCounitInv {S : Scheme.{u}} (P : AlgebraicSpace S) (N : P.Modules) :
    N ⟶ (CanonicalTwists.affineExtension P).obj
      (((CanonicalTwists.affineInclusionRingedHom P).modulePushforward).obj N) :=
  ((CanonicalTwists.affineInclusionRingedHom P).modulePushforward).preimage
    ((CanonicalTwists.affineExtensionAdjunction P).unit.app
      (((CanonicalTwists.affineInclusionRingedHom P).modulePushforward).obj N))

/-- The degree-`n` comparison `π^* 𝒜_n ⟶ 𝒪(n)`, obtained by extending
`chartAlgebraToTwist` from the affine étale basis. -/
def algebraToTwist (n : ℕ) :
    (Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n) ⟶
      CanonicalTwists.obj F hF (Int.ofNat n) :=
  moduleAffineCounitInv (toAlgebraicSpace F hF)
      ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)) ≫
    (CanonicalTwists.affineExtension (toAlgebraicSpace F hF)).map (affinePsiMap deg hF n)

/-- `algebraToTwist` is the dense-basis extension of `chartAlgebraToTwist`. -/
theorem algebraToTwist_eq (n : ℕ) :
    algebraToTwist deg hF n =
      moduleAffineCounitInv (toAlgebraicSpace F hF)
          ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)) ≫
        (CanonicalTwists.affineExtension (toAlgebraicSpace F hF)).map
          (affinePsiMap deg hF n) :=
  sorry

/-- The `𝒜_n`-section on an étale object of relative Proj obtained from a Serre-twist
section by the chartwise algebra-to-twist comparison. -/
def thetaAlgebraSection (U : smallEtaleSite (toAlgebraicSpace F hF)) (n : ℕ)
    (x : (CanonicalTwists.obj F hF (Int.ofNat n)).val.obj (op U)) :
    ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)).val.obj (op U) :=
  @Function.invFun
    (((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)).val.obj (op U))
    ((CanonicalTwists.obj F hF (Int.ofNat n)).val.obj (op U))
    ⟨0⟩ (((algebraToTwist deg hF n).val.app (op U)).hom) x

/-- Affine matching family for `r_* (L^{⊗ n}|_{U(ψ)})`, with components obtained by
applying `ψ` to the pulled-back algebra preimage of a twist section. -/
def thetaMatching (U : smallEtaleSite (toAlgebraicSpace F hF)) (n : ℕ)
    (x : (CanonicalTwists.obj F hF (Int.ofNat n)).val.obj (op U)) :
    CanonicalTwists.AffineMatching (canonicalMap f deg hF L ψ)
      ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L n)) U where
  value V j :=
    ((Modules.pullback (domain f deg L ψ).ι).map (ψ.hom n)).val.app (op V.obj)
      (((Modules.pullbackCompIso (domain f deg L ψ).ι f).inv.app (deg.obj n)).val.app
        (op V.obj)
        ((eqToHom
            (congrArg (fun h ↦ (Modules.pullback h).obj (deg.obj n))
              (canonicalMap_over_base f deg hF L ψ))).val.app (op V.obj)
          (((Modules.pullbackCompIso (canonicalMap f deg hF L ψ)
                (toAlgebraicSpace_hom F hF)).hom.app (deg.obj n)).val.app (op V.obj)
            (CanonicalTwists.directImageAtGraph (canonicalMap f deg hF L ψ)
              ((Modules.pullback (canonicalMap f deg hF L ψ)).obj
                ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj (deg.obj n)))
              U V j
              (((Modules.pullbackPushforwardAdjunction
                    (canonicalMap f deg hF L ψ)).unit.app
                  ((Modules.pullback (toAlgebraicSpace_hom F hF)).obj
                    (deg.obj n))).val.app (op U)
                (thetaAlgebraSection deg hF U n x))))))
  compatible := sorry

/-- Direct-image components of `θ` on an étale object of relative Proj. -/
def thetaDirectApp (U : (smallEtaleSite (toAlgebraicSpace F hF))ᵒᵖ) (n : ℕ)
    (s : (CanonicalTwists.obj F hF (Int.ofNat n)).val.obj U) :
    ((Modules.pushforward (canonicalMap f deg hF L ψ)).obj
        ((Modules.pullback (domain f deg L ψ).ι).obj
          (tensorPowerUnit L n))).val.obj U :=
  CanonicalTwists.sectionOfMatching (canonicalMap f deg hF L ψ)
    ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L n)) U.unop
    (thetaMatching f deg hF L ψ U.unop n s)

/-- The direct-image morphism `𝒪(n) ⟶ r_* (L^{⊗ n}|_{U(ψ)})`. -/
def thetaDirect (n : ℕ) :
    CanonicalTwists.obj F hF (Int.ofNat n) ⟶
      (Modules.pushforward (canonicalMap f deg hF L ψ)).obj
        ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L n)) where
  val :=
    { app := fun U ↦
        let M := (CanonicalTwists.obj F hF (Int.ofNat n)).val.obj U
        let N :=
          ((Modules.pushforward (canonicalMap f deg hF L ψ)).obj
              ((Modules.pullback (domain f deg L ψ).ι).obj
                (tensorPowerUnit L n))).val.obj U
        @ModuleCat.ofHom
          ((toAlgebraicSpace F hF).ringedSite.structureSheaf.obj.obj U) _
          M N M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
          { toFun := thetaDirectApp f deg hF L ψ U n
            map_add' := sorry
            map_smul' := sorry }
      naturality := sorry }

/-- The degree-`n` comparison `θ_n : r^* 𝒪(n) ⟶ L^{⊗ n}|_{U(ψ)}` is the adjoint of
`thetaDirect`. -/
def theta (n : ℕ) :
    (Modules.pullback (canonicalMap f deg hF L ψ)).obj
        (CanonicalTwists.obj F hF (Int.ofNat n)) ⟶
      (Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L n) :=
  ((Modules.pullbackPushforwardAdjunction (canonicalMap f deg hF L ψ)).homEquiv
      (CanonicalTwists.obj F hF (Int.ofNat n))
      ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L n))).symm
    (thetaDirect f deg hF L ψ n)

/-- The adjoint of `theta` recovers `thetaDirect`. -/
theorem theta_adjoint (n : ℕ) :
    ((Modules.pullbackPushforwardAdjunction (canonicalMap f deg hF L ψ)).homEquiv
        (CanonicalTwists.obj F hF (Int.ofNat n))
        ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L n)))
      (theta f deg hF L ψ n) =
      thetaDirect f deg hF L ψ n :=
  sorry

/-- Pushforward of `θ_d` along `π : underline{Proj}_Y(𝒜) ⟶ Y`, rewritten over `Y` via
`canonicalMap_over_base`. -/
def thetaPushforwardToBase (d : ℕ) :
    (Modules.pushforward (toAlgebraicSpace_hom F hF)).obj
        (CanonicalTwists.obj F hF (Int.ofNat d)) ⟶
      (Modules.pushforward ((domain f deg L ψ).ι ≫ f)).obj
        ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d)) :=
  (Modules.pushforward (toAlgebraicSpace_hom F hF)).map
      (thetaDirect f deg hF L ψ d) ≫
    (Modules.pushforwardComp (canonicalMap f deg hF L ψ)
        (toAlgebraicSpace_hom F hF)).hom.app
      ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d)) ≫
    eqToHom
      (congrArg
        (fun h ↦
          (Modules.pushforward h).obj
            ((Modules.pullback (domain f deg L ψ).ι).obj (tensorPowerUnit L d)))
        (canonicalMap_over_base f deg hF L ψ))

/-- The canonical section map `(U(ψ), r_{L,ψ}, θ)` determined by `ψ`. -/
def SectionMap.canonical : SectionMap f deg L hF ψ :=
  SectionMap.of f deg L hF ψ (RelativeProj.domain f deg L ψ)
    (canonicalMap f deg hF L ψ) (canonicalMap_over_base f deg hF L ψ)
    (RelativeProj.theta f deg hF L ψ) sorry sorry

/-- The domain of the canonical section map is `U(ψ)`. -/
theorem canonical_domain :
    (SectionMap.canonical f deg hF L ψ).domain = domain f deg L ψ :=
  rfl

/-- The morphism of the canonical section map is `canonicalMap`. -/
theorem canonical_map :
    (SectionMap.canonical f deg hF L ψ).map = canonicalMap f deg hF L ψ :=
  rfl

/-- The twist comparison of the canonical section map is `theta`. -/
theorem canonical_theta (n : ℕ) :
    (SectionMap.canonical f deg hF L ψ).theta n = theta f deg hF L ψ n :=
  sorry

/-- A point of `|X|` lies in `|U(ψ)|` when it arises from a test in `memDomain`. -/
theorem domain_pointsSet_eq (x : Points X) :
    x ∈ (domain f deg L ψ).pointsSet ↔
      ∃ (T : Over S) (w : ofOver T ⟶ X),
        (∃ y : Points (ofOver T), Points.map w y = x) ∧ memDomain f deg L ψ w :=
  sorry

/-- A test morphism `w` that lies in `U(ψ)` factors through the open inclusion. -/
def factorsThroughLift {T : Over S} (w : ofOver T ⟶ X)
    (hw : memDomain f deg L ψ w) : ofOver T ⟶ (domain f deg L ψ).X :=
  yonedaEquiv.symm ⟨yonedaEquiv w, sorry⟩

/-- The lift along `U(ψ) ⊂ X` recovers `w`. -/
theorem factorsThroughLift_comp {T : Over S} (w : ofOver T ⟶ X)
    (hw : memDomain f deg L ψ w) :
    factorsThroughLift f deg L ψ w hw ≫ (domain f deg L ψ).ι = w :=
  sorry

/-- The morphism `T ⟶ underline{Proj}_Y(𝒜)` classified by a `U(ψ)`-test. -/
def classifiedMap {T : Over S} (w : ofOver T ⟶ X)
    (hw : memDomain f deg L ψ w) : ofOver T ⟶ toAlgebraicSpace F hF :=
  yonedaEquiv.symm (canonicalPoint f deg hF L ψ T ⟨yonedaEquiv w, sorry⟩)

/-- `classifiedMap` is `pointOf` of the restricted quadruple on a quasi-compact test. -/
theorem classifiedMap_pointOf {T : Over S} [CompactSpace T.left]
    (w : ofOver T ⟶ X) (d : ℕ) (hd : 1 ≤ d)
    (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    classifiedMap f deg hF L ψ w (memDomain_of_epi f deg L ψ w d hd hEpi) =
      yonedaEquiv.symm
        (hF.pointOf T (restrictedQuadruple f deg L ψ w d hd hEpi)) :=
  sorry

/-- Epimorphicity of a restricted degree map is inherited by quasi-compact open
restrictions of the test. -/
theorem restrictedDegreeMap_epi_restrict {T : Over S} (w : ofOver T ⟶ X)
    (d : ℕ) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d))
    (V : T.left.Opens) [CompactSpace V.toScheme] :
    Epi (restrictedDegreeMap f deg L ψ (ofOverMap (openOverι T V) ≫ w) d) :=
  sorry

/-- The morphism `T ⟶ underline{Proj}_Y(𝒜)` obtained from Definition 71.11.3 by
gluing `hF.pointOf` of the restricted degree-`d` quadruple on quasi-compact opens
of `T`. -/
def classifiedMapOfDegree {T : Over S} (w : ofOver T ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    ofOver T ⟶ toAlgebraicSpace F hF :=
  yonedaEquiv.symm
    ((hF.qcLimit T).symm
      (ProjFunctor.QcCompatibleSystem.of
        (fun V _ ↦
          hF.pointOf (openOver T V)
            (restrictedQuadruple f deg L ψ
              (ofOverMap (openOverι T V) ≫ w) d hd
              (restrictedDegreeMap_epi_restrict f deg L ψ w d hEpi V)))
        sorry))

/-- On a quasi-compact test, `classifiedMapOfDegree` is Yoneda inversion of
`pointOf` of the restricted quadruple in the given degree. -/
theorem classifiedMapOfDegree_eq {T : Over S} [CompactSpace T.left]
    (w : ofOver T ⟶ X) (d : ℕ) (hd : 1 ≤ d)
    (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    classifiedMapOfDegree f deg hF L ψ w d hd hEpi =
      yonedaEquiv.symm
        (hF.pointOf T (restrictedQuadruple f deg L ψ w d hd hEpi)) :=
  sorry

/-- A section map is canonical when every scheme test that is an epimorphism in some
positive degree factors through the domain and is classified by the corresponding
restricted quadruple. -/
def SectionMap.IsCanonical (c : SectionMap f deg L hF ψ) : Prop :=
  ∀ (T : Over S) (w : ofOver T ⟶ X) (d : ℕ) (hd : 1 ≤ d)
      (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)),
    ∃ lift : ofOver T ⟶ c.domain.X,
      lift ≫ c.domain.ι = w ∧
        lift ≫ c.map =
          classifiedMapOfDegree f deg hF L ψ w d hd hEpi

/-- Canonicity is the scheme-test factoring and classification property. -/
theorem SectionMap.isCanonical_spec (c : SectionMap f deg L hF ψ) :
    SectionMap.IsCanonical f deg hF L ψ c ↔
      ∀ (T : Over S) (w : ofOver T ⟶ X) (d : ℕ) (hd : 1 ≤ d)
          (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)),
        ∃ lift : ofOver T ⟶ c.domain.X,
          lift ≫ c.domain.ι = w ∧
            lift ≫ c.map =
              classifiedMapOfDegree f deg hF L ψ w d hd hEpi :=
  sorry

/-- The constructed triple is canonical. -/
theorem canonical_isCanonical :
    SectionMap.IsCanonical f deg hF L ψ
      (SectionMap.canonical f deg hF L ψ) :=
  sorry

/-- A canonical section map agrees with `SectionMap.canonical`. -/
theorem eq_canonical (c : SectionMap f deg L hF ψ)
    (hc : SectionMap.IsCanonical f deg hF L ψ c) :
    c = SectionMap.canonical f deg hF L ψ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
