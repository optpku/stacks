/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Algebra
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback

/-!
# Étale characterization of relative projective-spectrum maps of algebraic spaces

A graded algebra map determines a partial relative-Proj map, characterized up
to a unique compatible domain isomorphism by its restrictions to étale schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open AlgebraicGeometry.AlgebraicSpace.ReasLibPullback
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProjMap

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
variable [𝒜.IsCommutative] [ℬ.IsCommutative]
variable {degA : DegreePieces 𝒜} {degB : DegreePieces ℬ}

/-- The scheme-level algebra map induced by `ψ|_W`, obtained by transporting
`pullbackHom φ g` along identifications of the presentation algebras with
`g^* 𝒜` and `g^* ℬ`. -/
def inducedHom {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (eA : P𝒜W.algebra ≅ pullbackAlgebra g degA)
    (eB : PℬW.algebra ≅ pullbackAlgebra g degB) :
    P𝒜W.algebra ⟶ PℬW.algebra :=
  eA.hom ≫ pullbackHom φ g degA degB ≫ eB.inv

/-- `inducedHom` is transport of `pullbackHom` along the presentation identifications. -/
theorem inducedHom_eq {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (eA : P𝒜W.algebra ≅ pullbackAlgebra g degA)
    (eB : PℬW.algebra ≅ pullbackAlgebra g degB) :
    inducedHom φ eA eB = eA.hom ≫ pullbackHom φ g degA degB ≫ eB.inv :=
  rfl

/-- Degreewise, `inducedHom` is the conjugate of `pullbackHom` by the presentation
identifications. -/
theorem inducedHom_hom {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (eA : P𝒜W.algebra ≅ pullbackAlgebra g degA)
    (eB : PℬW.algebra ≅ pullbackAlgebra g degB) (n : ℤ) :
    (inducedHom φ eA eB).hom n =
      (eA.hom).hom n ≫ (pullbackHom φ g degA degB).hom n ≫ (eB.inv).hom n :=
  sorry

omit [𝒜.IsQuasicoherent] [𝒜.IsCommutative] in
/-- The canonical maps between the sheaf fibre product and the categorical
pullback are mutually inverse. -/
theorem overSpaceIso_laws {W : Over S} (g : ofOver W ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg) :
    let hom :=
      pullback.lift
        (pullbackOverSnd g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal)
        (pullbackOverFst g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal)
        (isPullback g (toAlgebraicSpace_hom F hF)).w.symm
    let inv :=
      pullbackLift g (toAlgebraicSpace_hom F hF)
        (pullback.snd (toAlgebraicSpace_hom F hF) g)
        (pullback.fst (toAlgebraicSpace_hom F hF) g)
        (@pullback.condition _ _ _ _ _ (toAlgebraicSpace_hom F hF) g _).symm
    hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ :=
  sorry

/-- The canonical identification of the sheaf fibre product `W ×_X P` with the
categorical pullback `P ×_X W`, uniquely determined by commuting with the
projections to `P` and to `W`. -/
def overSpaceIso {W : Over S} (g : ofOver W ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg) :
    pullbackOverSpace g F hF ≅ pullback (toAlgebraicSpace_hom F hF) g where
  hom :=
    pullback.lift
      (pullbackOverSnd g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal)
      (pullbackOverFst g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal)
      (isPullback g (toAlgebraicSpace_hom F hF)).w.symm
  inv :=
    pullbackLift g (toAlgebraicSpace_hom F hF)
      (pullback.snd (toAlgebraicSpace_hom F hF) g)
      (pullback.fst (toAlgebraicSpace_hom F hF) g)
      (@pullback.condition _ _ _ _ _ (toAlgebraicSpace_hom F hF) g _).symm
  hom_inv_id := (overSpaceIso_laws g F hF).1
  inv_hom_id := (overSpaceIso_laws g F hF).2

/-- `overSpaceIso.hom` recovers the projection to `P`. -/
theorem overSpaceIso_fst {W : Over S} (g : ofOver W ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg) :
    (overSpaceIso g F hF).hom ≫ pullback.fst (toAlgebraicSpace_hom F hF) g =
      pullbackOverSnd g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal :=
  sorry

/-- `overSpaceIso.hom` recovers the projection to `W`. -/
theorem overSpaceIso_snd {W : Over S} (g : ofOver W ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg) :
    (overSpaceIso g F hF).hom ≫ pullback.snd (toAlgebraicSpace_hom F hF) g =
      pullbackOverFst g (toAlgebraicSpace_hom F hF) X.isSheaf X.representableDiagonal :=
  sorry

/-- The composite identification `underline{Proj}_W(g^* 𝒜) ≅ P ×_X W`, using
`baseChangeIso` and the canonical fibre-product symmetry. -/
def relativeProjPullbackIso {W : Over S} (g : ofOver W ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)] :
    ofOver (relativeProjOver g deg) ≅ pullback (toAlgebraicSpace_hom F hF) g :=
  baseChangeIso g F hF ≪≫ overSpaceIso g F hF

/-- The composite identification is `baseChangeIso` followed by `overSpaceIso`. -/
theorem relativeProjPullbackIso_eq {W : Over S} (g : ofOver W ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)] :
    relativeProjPullbackIso g F hF = baseChangeIso g F hF ≪≫ overSpaceIso g F hF :=
  rfl

/-- The composite identification commutes with the projections to `P`. -/
theorem relativeProjPullbackIso_fst {W : Over S} (g : ofOver W ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)] :
    (relativeProjPullbackIso g F hF).hom ≫
        pullback.fst (toAlgebraicSpace_hom F hF) g =
      (baseChangeIso g F hF).hom ≫
        pullbackOverSnd g (toAlgebraicSpace_hom F hF) X.isSheaf
          X.representableDiagonal :=
  sorry

/-- The composite identification commutes with the projections to `W`. -/
theorem relativeProjPullbackIso_snd {W : Over S} (g : ofOver W ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)] :
    (relativeProjPullbackIso g F hF).hom ≫
        pullback.snd (toAlgebraicSpace_hom F hF) g =
      (baseChangeIso g F hF).hom ≫
        pullbackOverFst g (toAlgebraicSpace_hom F hF) X.isSheaf
          X.representableDiagonal :=
  sorry

/-- Restriction of `restrictTheta` to the scheme-level open of `schemeMap`. -/
def restrictThetaOnScheme
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    (schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB))
    (domainIso :
      ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
        (restrictDomain r g).X)
    (n : ℤ) :
    (Modules.restrictToScheme
        (openOver (relativeProjOver g degB) schemeMap.domain)).obj
      ((Modules.pullback domainIso.hom).obj
        ((Modules.pullback (restrictMap r g)).obj
          ((Modules.pullback (pullback.fst (toAlgebraicSpace_hom FA hFA) g)).obj
            ((CanonicalTwists.family FA hFA).obj n)))) ⟶
      (Modules.restrictToScheme
          (openOver (relativeProjOver g degB) schemeMap.domain)).obj
        ((Modules.pullback domainIso.hom).obj
          ((Modules.pullback (restrictDomain r g).ι).obj
            ((Modules.pullback (pullback.fst (toAlgebraicSpace_hom FB hFB) g)).obj
              ((CanonicalTwists.family FB hFB).obj n)))) :=
  (Modules.restrictToScheme
      (openOver (relativeProjOver g degB) schemeMap.domain)).map
    ((Modules.pullback domainIso.hom).map (restrictTheta r g n))

/-- `restrictThetaOnScheme` is restriction of the pullback of `restrictTheta`. -/
theorem restrictThetaOnScheme_eq
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    (schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB))
    (domainIso :
      ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
        (restrictDomain r g).X)
    (n : ℤ) :
    restrictThetaOnScheme schemeMap domainIso n =
      (Modules.restrictToScheme
          (openOver (relativeProjOver g degB) schemeMap.domain)).map
        ((Modules.pullback domainIso.hom).map (restrictTheta r g n)) :=
  rfl

/-- The Serre twist of `underline{Proj}_W(g^* 𝒜)` as a module on the algebraic
space `ofOver (relativeProjOver g deg)`, obtained by transporting `𝒪_P(n)` along
`relativeProjPullbackIso.hom`. -/
def relativeProjSerreTwist {W : Over S} (g : ofOver W ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    (n : ℤ) : (ofOver (relativeProjOver g deg)).Modules :=
  (Modules.pullback (relativeProjPullbackIso g F hF).hom).obj
    ((Modules.pullback (pullback.fst (toAlgebraicSpace_hom F hF) g)).obj
      ((CanonicalTwists.family F hF).obj n))

/-- `relativeProjSerreTwist` is the pullback of `𝒪_P(n)` along
`relativeProjPullbackIso.hom`. -/
theorem relativeProjSerreTwist_eq {W : Over S} (g : ofOver W ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    (n : ℤ) :
    relativeProjSerreTwist g F hF n =
      (Modules.pullback (relativeProjPullbackIso g F hF).hom).obj
        ((Modules.pullback (pullback.fst (toAlgebraicSpace_hom F hF) g)).obj
          ((CanonicalTwists.family F hF).obj n)) :=
  rfl

/-- The transported Serre twist is quasi-coherent. -/
def relativeProjSerreTwist_isQuasicoherent {W : Over S} (g : ofOver W ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    (n : ℤ) : (relativeProjSerreTwist g F hF n).IsQuasicoherent :=
  sorry

/-- The Serre twist of `relativeProjToZLeft`, obtained by restricting the
transported canonical twist `𝒪_P(n)` to the representing scheme. -/
def presentationSerreTwist {W : Over S} (g : ofOver W ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    (n : ℤ) : (relativeProjOver g deg).left.Modules :=
  (Modules.restrictToScheme (relativeProjOver g deg)).obj
    (relativeProjSerreTwist g F hF n)

/-- `presentationSerreTwist` is `restrictToScheme` of `relativeProjSerreTwist`. -/
theorem presentationSerreTwist_eq {W : Over S} (g : ofOver W ⟶ X)
    (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
    (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    (n : ℤ) :
    presentationSerreTwist g F hF n =
      (Modules.restrictToScheme (relativeProjOver g deg)).obj
        (relativeProjSerreTwist g F hF n) :=
  rfl

/-- An algebra identification of a relative-Proj presentation of
`underline{Proj}_W(g^* 𝒜)` with `g^* 𝒜` is chart-compatible when it is the
equality identification with `pullbackAlgebra` and the presentation twists are
the Serre twists of `relativeProjToZLeft` transported from `CanonicalTwists`
along `relativeProjPullbackIso`. -/
structure IsChartCompatibleAlgebraIso
    {W : Over S} (g : ofOver W ⟶ X) (F : ProjFunctor X 𝒜)
    {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg)
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    (P : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g deg))
    (e : P.algebra ≅ pullbackAlgebra g deg) : Prop where
  /-- The presentation algebra is `g^* 𝒜`. -/
  algebra_eq : P.algebra = pullbackAlgebra g deg
  /-- The identification is the reflexivity iso of `algebra_eq`. -/
  iso_eq : e = eqToIso algebra_eq
  /-- Presentation twists are the Serre twists of `relativeProjToZLeft`. -/
  twist_eq : ∀ n : ℤ, P.twist n = presentationSerreTwist g F hF n

namespace IsChartCompatibleAlgebraIso

/-- The reflexivity identification of a presentation whose algebra is `g^* 𝒜`
and whose twists are the transported Serre twists. -/
theorem ofEq {W : Over S} {g : ofOver W ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    {P : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g deg)}
    (h : P.algebra = pullbackAlgebra g deg)
    (htwist : ∀ n : ℤ, P.twist n = presentationSerreTwist g F hF n) :
    IsChartCompatibleAlgebraIso g F hF P (eqToIso h) where
  algebra_eq := h
  iso_eq := rfl
  twist_eq := htwist

/-- Chart-compatibility means the presentation algebra equals `g^* 𝒜`, the
identifying iso is reflexivity, and the twists are the transported Serre
twists of `relativeProjToZLeft`. -/
theorem spec {W : Over S} {g : ofOver W ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    {P : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g deg)}
    {e : P.algebra ≅ pullbackAlgebra g deg}
    (h : IsChartCompatibleAlgebraIso g F hF P e) :
    P.algebra = pullbackAlgebra g deg ∧ e = eqToIso h.algebra_eq ∧
      ∀ n : ℤ, P.twist n = presentationSerreTwist g F hF n :=
  sorry

/-- The pinned identification of a chart-compatible presentation twist with the
Serre twist of `relativeProjToZLeft`. -/
def twistIso {W : Over S} {g : ofOver W ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    {P : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g deg)}
    {e : P.algebra ≅ pullbackAlgebra g deg}
    (h : IsChartCompatibleAlgebraIso g F hF P e) (n : ℤ) :
    P.twist n ≅ presentationSerreTwist g F hF n :=
  eqToIso (h.twist_eq n)

/-- `twistIso` is `eqToIso` of `twist_eq`. -/
theorem twistIso_eq {W : Over S} {g : ofOver W ⟶ X} {F : ProjFunctor X 𝒜}
    {deg : DegreePieces 𝒜} {hF : F.IsAssociatedToQuadruples deg}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g deg)]
    {P : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g deg)}
    {e : P.algebra ≅ pullbackAlgebra g deg}
    (h : IsChartCompatibleAlgebraIso g F hF P e) (n : ℤ) :
    twistIso h n = eqToIso (h.twist_eq n) :=
  rfl

end IsChartCompatibleAlgebraIso

/-- On a chart-compatible presentation, `inducedHom` is `pullbackHom` transported
along the equality identification with `g^* 𝒜`. -/
theorem inducedHom_of_chartCompatible {W : Over S} {g : ofOver W ⟶ X}
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    (hA : IsChartCompatibleAlgebraIso g FA hFA P𝒜W eA)
    (hB : IsChartCompatibleAlgebraIso g FB hFB PℬW eB)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ) :
    inducedHom φ eA eB =
      eqToHom hA.algebra_eq ≫ pullbackHom φ g degA degB ≫ eqToHom hB.algebra_eq.symm :=
  sorry

/-- The scheme morphism over `S` underlying a scheme-level relative projective
spectrum map of `ψ|_W`. -/
def schemeMapOverHom
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)}
    (schemeMap_over_S :
      schemeMap.map ≫ (relativeProjOver g degA).hom =
        schemeMap.domain.ι ≫ (relativeProjOver g degB).hom) :
    openOver (relativeProjOver g degB) schemeMap.domain ⟶ relativeProjOver g degA :=
  Over.homMk schemeMap.map schemeMap_over_S

/-- `schemeMapOverHom` is `Over.homMk` of the scheme-level map. -/
theorem schemeMapOverHom_left
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)}
    (schemeMap_over_S :
      schemeMap.map ≫ (relativeProjOver g degA).hom =
        schemeMap.domain.ι ≫ (relativeProjOver g degB).hom) :
    (schemeMapOverHom schemeMap_over_S).left = schemeMap.map :=
  rfl

/-- Canonical source transport for `θ`: pullback of the pinned presentation Serre
twist along `schemeMap`, then `relativeProjPullbackIso` and `domainIso`. -/
def thetaSourceIso
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    {schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)}
    {domainIso :
      ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
        (restrictDomain r g).X}
    (schemeMap_over_S :
      schemeMap.map ≫ (relativeProjOver g degA).hom =
        schemeMap.domain.ι ≫ (relativeProjOver g degB).hom)
    (map_eq :
      domainIso.hom ≫ restrictMap r g =
        ofOverMap (schemeMapOverHom schemeMap_over_S) ≫
          (relativeProjPullbackIso g FA hFA).hom)
    (hA : IsChartCompatibleAlgebraIso g FA hFA P𝒜W eA) (n : ℤ) :
    (Scheme.Modules.pullback schemeMap.map).obj (P𝒜W.twist n) ≅
      (Modules.restrictToScheme
          (openOver (relativeProjOver g degB) schemeMap.domain)).obj
        ((Modules.pullback domainIso.hom).obj
          ((Modules.pullback (restrictMap r g)).obj
            ((Modules.pullback (pullback.fst (toAlgebraicSpace_hom FA hFA) g)).obj
              ((CanonicalTwists.family FA hFA).obj n)))) :=
  let t := schemeMapOverHom schemeMap_over_S
  let Mfst :=
    (Modules.pullback (pullback.fst (toAlgebraicSpace_hom FA hFA) g)).obj
      ((CanonicalTwists.family FA hFA).obj n)
  (Scheme.Modules.pullback schemeMap.map).mapIso
      (IsChartCompatibleAlgebraIso.twistIso hA n) ≪≫
    (@Modules.RestrictToScheme.restrictPullbackIso S _ _ t
          (relativeProjSerreTwist g FA hFA n)
          (relativeProjSerreTwist_isQuasicoherent g FA hFA n)).symm ≪≫
    (Modules.restrictToScheme
        (openOver (relativeProjOver g degB) schemeMap.domain)).mapIso
      ((Modules.pullbackCompIso (ofOverMap t)
          (relativeProjPullbackIso g FA hFA).hom).app Mfst ≪≫
        eqToIso (congrArg (fun f ↦ (Modules.pullback f).obj Mfst)
          map_eq.symm) ≪≫
        (Modules.pullbackCompIso domainIso.hom (restrictMap r g)).symm.app Mfst)

/-- `thetaSourceIso` is the composite of `twistIso`, the restriction/pullback comparison, and
the `relativeProjPullbackIso`/`domainIso`/`map_eq` transport. -/
theorem thetaSourceIso_eq
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    {schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)}
    {domainIso :
      ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
        (restrictDomain r g).X}
    (schemeMap_over_S :
      schemeMap.map ≫ (relativeProjOver g degA).hom =
        schemeMap.domain.ι ≫ (relativeProjOver g degB).hom)
    (map_eq :
      domainIso.hom ≫ restrictMap r g =
        ofOverMap (schemeMapOverHom schemeMap_over_S) ≫
          (relativeProjPullbackIso g FA hFA).hom)
    (hA : IsChartCompatibleAlgebraIso g FA hFA P𝒜W eA) (n : ℤ) :
    thetaSourceIso schemeMap_over_S map_eq hA n =
      let t := schemeMapOverHom schemeMap_over_S
      let Mfst :=
        (Modules.pullback (pullback.fst (toAlgebraicSpace_hom FA hFA) g)).obj
          ((CanonicalTwists.family FA hFA).obj n)
      (Scheme.Modules.pullback schemeMap.map).mapIso
          (IsChartCompatibleAlgebraIso.twistIso hA n) ≪≫
        (@Modules.RestrictToScheme.restrictPullbackIso S _ _ t
          (relativeProjSerreTwist g FA hFA n)
          (relativeProjSerreTwist_isQuasicoherent g FA hFA n)).symm ≪≫
        (Modules.restrictToScheme
            (openOver (relativeProjOver g degB) schemeMap.domain)).mapIso
          ((Modules.pullbackCompIso (ofOverMap t)
              (relativeProjPullbackIso g FA hFA).hom).app Mfst ≪≫
            eqToIso (congrArg (fun f ↦ (Modules.pullback f).obj Mfst)
              map_eq.symm) ≪≫
            (Modules.pullbackCompIso domainIso.hom
              (restrictMap r g)).symm.app Mfst) :=
  rfl

/-- Canonical target transport for `θ`: restriction of the pinned presentation
Serre twist along the scheme-level domain, then `relativeProjPullbackIso` and
`domainIso`. -/
def thetaTargetIso
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    {schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)}
    {domainIso :
      ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
        (restrictDomain r g).X}
    (domain_over_Q :
      domainIso.hom ≫ (restrictDomain r g).ι =
        ofOverMap (openOverι (relativeProjOver g degB) schemeMap.domain) ≫
          (relativeProjPullbackIso g FB hFB).hom)
    (hB : IsChartCompatibleAlgebraIso g FB hFB PℬW eB) (n : ℤ) :
    (PℬW.twist n).restrict schemeMap.domain.ι ≅
      (Modules.restrictToScheme
          (openOver (relativeProjOver g degB) schemeMap.domain)).obj
        ((Modules.pullback domainIso.hom).obj
          ((Modules.pullback (restrictDomain r g).ι).obj
            ((Modules.pullback (pullback.fst (toAlgebraicSpace_hom FB hFB) g)).obj
              ((CanonicalTwists.family FB hFB).obj n)))) :=
  let ι := openOverι (relativeProjOver g degB) schemeMap.domain
  let Mfst :=
    (Modules.pullback (pullback.fst (toAlgebraicSpace_hom FB hFB) g)).obj
      ((CanonicalTwists.family FB hFB).obj n)
  (Scheme.Modules.restrictFunctorIsoPullback schemeMap.domain.ι).app (PℬW.twist n) ≪≫
    (Scheme.Modules.pullback schemeMap.domain.ι).mapIso
      (IsChartCompatibleAlgebraIso.twistIso hB n) ≪≫
    (@Modules.RestrictToScheme.restrictPullbackIso S _ _ ι
          (relativeProjSerreTwist g FB hFB n)
          (relativeProjSerreTwist_isQuasicoherent g FB hFB n)).symm ≪≫
    (Modules.restrictToScheme
        (openOver (relativeProjOver g degB) schemeMap.domain)).mapIso
      ((Modules.pullbackCompIso (ofOverMap ι)
          (relativeProjPullbackIso g FB hFB).hom).app Mfst ≪≫
        eqToIso (congrArg (fun f ↦ (Modules.pullback f).obj Mfst)
          domain_over_Q.symm) ≪≫
        (Modules.pullbackCompIso domainIso.hom
          (restrictDomain r g).ι).symm.app Mfst)

/-- `thetaTargetIso` is the composite of `restrictFunctorIsoPullback`, `twistIso`,
the restriction/pullback comparison, and the `relativeProjPullbackIso`/`domainIso` transport. -/
theorem thetaTargetIso_eq
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    {schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)}
    {domainIso :
      ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
        (restrictDomain r g).X}
    (domain_over_Q :
      domainIso.hom ≫ (restrictDomain r g).ι =
        ofOverMap (openOverι (relativeProjOver g degB) schemeMap.domain) ≫
          (relativeProjPullbackIso g FB hFB).hom)
    (hB : IsChartCompatibleAlgebraIso g FB hFB PℬW eB) (n : ℤ) :
    thetaTargetIso domain_over_Q hB n =
      let ι := openOverι (relativeProjOver g degB) schemeMap.domain
      let Mfst :=
        (Modules.pullback (pullback.fst (toAlgebraicSpace_hom FB hFB) g)).obj
          ((CanonicalTwists.family FB hFB).obj n)
      (Scheme.Modules.restrictFunctorIsoPullback schemeMap.domain.ι).app
          (PℬW.twist n) ≪≫
        (Scheme.Modules.pullback schemeMap.domain.ι).mapIso
          (IsChartCompatibleAlgebraIso.twistIso hB n) ≪≫
        (@Modules.RestrictToScheme.restrictPullbackIso S _ _ ι
          (relativeProjSerreTwist g FB hFB n)
          (relativeProjSerreTwist_isQuasicoherent g FB hFB n)).symm ≪≫
        (Modules.restrictToScheme
            (openOver (relativeProjOver g degB) schemeMap.domain)).mapIso
          ((Modules.pullbackCompIso (ofOverMap ι)
              (relativeProjPullbackIso g FB hFB).hom).app Mfst ≪≫
            eqToIso (congrArg (fun f ↦ (Modules.pullback f).obj Mfst)
              domain_over_Q.symm) ≪≫
            (Modules.pullbackCompIso domainIso.hom
              (restrictDomain r g).ι).symm.app Mfst) :=
  rfl

/-- The pinned sheaf-level `θ` square: `schemeMap.theta n` equals the restricted
algebraic-space comparison after `thetaSourceIso` and `thetaTargetIso`. -/
def thetaCompatible
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    {schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)}
    {domainIso :
      ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
        (restrictDomain r g).X}
    (schemeMap_over_S :
      schemeMap.map ≫ (relativeProjOver g degA).hom =
        schemeMap.domain.ι ≫ (relativeProjOver g degB).hom)
    (map_eq :
      domainIso.hom ≫ restrictMap r g =
        ofOverMap (schemeMapOverHom schemeMap_over_S) ≫
          (relativeProjPullbackIso g FA hFA).hom)
    (domain_over_Q :
      domainIso.hom ≫ (restrictDomain r g).ι =
        ofOverMap (openOverι (relativeProjOver g degB) schemeMap.domain) ≫
          (relativeProjPullbackIso g FB hFB).hom)
    (hA : IsChartCompatibleAlgebraIso g FA hFA P𝒜W eA)
    (hB : IsChartCompatibleAlgebraIso g FB hFB PℬW eB) (n : ℤ) : Prop :=
  schemeMap.theta n ≫ (thetaTargetIso domain_over_Q hB n).hom =
    (thetaSourceIso schemeMap_over_S map_eq hA n).hom ≫
      restrictThetaOnScheme schemeMap domainIso n

/-- `thetaCompatible` is the pinned `θ` commuting square. -/
theorem thetaCompatible_iff
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    {schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)}
    {domainIso :
      ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
        (restrictDomain r g).X}
    (schemeMap_over_S :
      schemeMap.map ≫ (relativeProjOver g degA).hom =
        schemeMap.domain.ι ≫ (relativeProjOver g degB).hom)
    (map_eq :
      domainIso.hom ≫ restrictMap r g =
        ofOverMap (schemeMapOverHom schemeMap_over_S) ≫
          (relativeProjPullbackIso g FA hFA).hom)
    (domain_over_Q :
      domainIso.hom ≫ (restrictDomain r g).ι =
        ofOverMap (openOverι (relativeProjOver g degB) schemeMap.domain) ≫
          (relativeProjPullbackIso g FB hFB).hom)
    (hA : IsChartCompatibleAlgebraIso g FA hFA P𝒜W eA)
    (hB : IsChartCompatibleAlgebraIso g FB hFB PℬW eB) (n : ℤ) :
    thetaCompatible schemeMap_over_S map_eq domain_over_Q hA hB n ↔
      schemeMap.theta n ≫ (thetaTargetIso domain_over_Q hB n).hom =
        (thetaSourceIso schemeMap_over_S map_eq hA n).hom ≫
          restrictThetaOnScheme schemeMap domainIso n :=
  sorry

/-- A scheme-level triple is affine-compatible when it agrees with the canonical
scheme construction over every affine open of the base. -/
def IsAffineCompatible
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)) :
    Prop :=
  ∀ V : W.left.affineOpens,
    Nonempty
      (AlgebraicGeometry.RelativeProjMap.AffineChartCompatibility
        P𝒜W PℬW (inducedHom φ eA eB) schemeMap V)

/-- `IsAffineCompatible` is affine-chart compatibility of the scheme-level triple
over every affine open of `W`. -/
theorem IsAffineCompatible_iff
    {W : Over S} {g : ofOver W ⟶ X}
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    {P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)}
    {PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)}
    {eA : P𝒜W.algebra ≅ pullbackAlgebra g degA}
    {eB : PℬW.algebra ≅ pullbackAlgebra g degB}
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)) :
    IsAffineCompatible φ schemeMap ↔
      ∀ V : W.left.affineOpens,
        Nonempty
          (AlgebraicGeometry.RelativeProjMap.AffineChartCompatibility
            P𝒜W PℬW (inducedHom φ eA eB) schemeMap V) :=
  sorry

/-- Comparison data identify a restricted partial relative-Proj map with the
scheme construction of the pulled-back algebra map. They include the algebra,
Serre-twist, domain, morphism, and integral-degree comparison identifications. -/
structure EtaleChartCompatibility
    {FA : ProjFunctor X 𝒜} (hFA : FA.IsAssociatedToQuadruples degA)
    {FB : ProjFunctor X ℬ} (hFB : FB.IsAssociatedToQuadruples degB)
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ)
    {W : Over S} (g : ofOver W ⟶ X) [Etale g]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)] where
  /-- A relative-Proj presentation of `underline{Proj}_W(g^* 𝒜)`. -/
  P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA)
  /-- A relative-Proj presentation of `underline{Proj}_W(g^* ℬ)`. -/
  PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB)
  /-- Algebra identification of the source presentation with `g^* 𝒜`. -/
  eA : P𝒜W.algebra ≅ pullbackAlgebra g degA
  /-- Algebra identification of the target presentation with `g^* ℬ`. -/
  eB : PℬW.algebra ≅ pullbackAlgebra g degB
  /-- The source identification is the canonical equality with `g^* 𝒜` and the
  Serre twists of `relativeProjToZLeft`. -/
  algebraA_chartCompatible : IsChartCompatibleAlgebraIso g FA hFA P𝒜W eA
  /-- The target identification is the canonical equality with `g^* ℬ` and the
  Serre twists of `relativeProjToZLeft`. -/
  algebraB_chartCompatible : IsChartCompatibleAlgebraIso g FB hFB PℬW eB
  /-- A scheme-level relative-Proj map for the pulled-back algebra homomorphism. -/
  schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB)
  /-- The scheme triple agrees with the canonical construction on every affine base open. -/
  absCompatibility : IsAffineCompatible φ schemeMap
  /-- Identification of the scheme-level domain with `U(ψ) ×_X W`. -/
  domainIso :
    ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
      (restrictDomain r g).X
  /-- The scheme-level morphism is a morphism of schemes over `S`. -/
  schemeMap_over_S :
    schemeMap.map ≫ (relativeProjOver g degA).hom =
      schemeMap.domain.ι ≫ (relativeProjOver g degB).hom
  /-- The domain identification commutes with the inclusions into `Q ×_X W`. -/
  domain_over_Q :
    domainIso.hom ≫ (restrictDomain r g).ι =
      ofOverMap (openOverι (relativeProjOver g degB) schemeMap.domain) ≫
        (relativeProjPullbackIso g FB hFB).hom
  /-- The restricted morphism agrees with the scheme-level map after identification. -/
  map_eq :
    domainIso.hom ≫ restrictMap r g =
      ofOverMap (schemeMapOverHom schemeMap_over_S) ≫
        (relativeProjPullbackIso g FA hFA).hom
  /-- After the pinned transports `thetaSourceIso` and `thetaTargetIso`,
  `schemeMap.theta n` equals the restricted algebraic-space comparison for
  every `n : ℤ`. -/
  theta_eq :
    ∀ n : ℤ,
      thetaCompatible schemeMap_over_S map_eq domain_over_Q
        algebraA_chartCompatible algebraB_chartCompatible n

namespace EtaleChartCompatibility

/-- Algebra, twist, domain, and morphism identifications satisfying the comparison
squares determine an étale-chart comparison. -/
def of
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X} [Etale g]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    (P𝒜W : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degA))
    (PℬW : Scheme.Hom.RelativeProjPresentation (relativeProjToZLeft g degB))
    (eA : P𝒜W.algebra ≅ pullbackAlgebra g degA)
    (eB : PℬW.algebra ≅ pullbackAlgebra g degB)
    (algebraA_chartCompatible : IsChartCompatibleAlgebraIso g FA hFA P𝒜W eA)
    (algebraB_chartCompatible : IsChartCompatibleAlgebraIso g FB hFB PℬW eB)
    (schemeMap : AlgebraicGeometry.RelativeProjMap P𝒜W PℬW (inducedHom φ eA eB))
    (absCompatibility : IsAffineCompatible φ schemeMap)
    (domainIso :
      ofOver (openOver (relativeProjOver g degB) schemeMap.domain) ≅
        (restrictDomain r g).X)
    (schemeMap_over_S :
      schemeMap.map ≫ (relativeProjOver g degA).hom =
        schemeMap.domain.ι ≫ (relativeProjOver g degB).hom)
    (domain_over_Q :
      domainIso.hom ≫ (restrictDomain r g).ι =
        ofOverMap (openOverι (relativeProjOver g degB) schemeMap.domain) ≫
          (relativeProjPullbackIso g FB hFB).hom)
    (map_eq :
      domainIso.hom ≫ restrictMap r g =
        ofOverMap (schemeMapOverHom schemeMap_over_S) ≫
          (relativeProjPullbackIso g FA hFA).hom)
    (theta_eq :
      ∀ n : ℤ,
        thetaCompatible schemeMap_over_S map_eq domain_over_Q
          algebraA_chartCompatible algebraB_chartCompatible n) :
    EtaleChartCompatibility hFA hFB r g where
  P𝒜W := P𝒜W
  PℬW := PℬW
  eA := eA
  eB := eB
  algebraA_chartCompatible := algebraA_chartCompatible
  algebraB_chartCompatible := algebraB_chartCompatible
  schemeMap := schemeMap
  absCompatibility := absCompatibility
  domainIso := domainIso
  schemeMap_over_S := schemeMap_over_S
  domain_over_Q := domain_over_Q
  map_eq := map_eq
  theta_eq := theta_eq

/-- Transport étale-chart comparison along an equality of algebraic-space triples. -/
def ofEq
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r r' : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X} [Etale g]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    (h : r = r') (C : EtaleChartCompatibility hFA hFB r g) :
    EtaleChartCompatibility hFA hFB r' g :=
  h ▸ C

/-- An étale-chart comparison identifies the presentation algebras and twists,
the map on every affine base open, the domain and morphism over the base, and
the comparison sheaf maps in every integral degree. -/
theorem spec
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X} [Etale g]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    (C : EtaleChartCompatibility hFA hFB r g) :
    IsChartCompatibleAlgebraIso g FA hFA C.P𝒜W C.eA ∧
      IsChartCompatibleAlgebraIso g FB hFB C.PℬW C.eB ∧
      (∀ n : ℤ, C.P𝒜W.twist n = presentationSerreTwist g FA hFA n) ∧
      (∀ n : ℤ, C.PℬW.twist n = presentationSerreTwist g FB hFB n) ∧
      inducedHom φ C.eA C.eB =
        C.eA.hom ≫ pullbackHom φ g degA degB ≫ C.eB.inv ∧
      IsAffineCompatible φ C.schemeMap ∧
      C.domainIso.hom ≫ (restrictDomain r g).ι =
        ofOverMap (openOverι (relativeProjOver g degB) C.schemeMap.domain) ≫
          (relativeProjPullbackIso g FB hFB).hom ∧
      C.domainIso.hom ≫ restrictMap r g =
        ofOverMap (schemeMapOverHom C.schemeMap_over_S) ≫
          (relativeProjPullbackIso g FA hFA).hom ∧
      ∀ n : ℤ,
        thetaCompatible C.schemeMap_over_S C.map_eq C.domain_over_Q
          C.algebraA_chartCompatible C.algebraB_chartCompatible n :=
  sorry

/-- An étale-chart comparison gives affine compatibility of the scheme triple
over every affine open of the base. -/
theorem restrictTheta_degreeCommutes
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    {W : Over S} {g : ofOver W ⟶ X} [Etale g]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
    [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)]
    (C : EtaleChartCompatibility hFA hFB r g) :
    IsAffineCompatible φ C.schemeMap :=
  sorry

end EtaleChartCompatibility

/-- The integral-degree comparison preserves the unit and multiplication of
the canonical Serre-twist algebras. -/
def IsGradedAlgebraMap
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ)
    : Prop :=
    (Modules.structureModulePullbackInv r.map ≫
          (Modules.pullback r.map).map (CanonicalTwists.family FA hFA).unit ≫
            r.theta 0 =
        Modules.structureModulePullbackInv r.domain.ι ≫
          (Modules.pullback r.domain.ι).map (CanonicalTwists.family FB hFB).unit) ∧
      ∀ n m : ℤ,
        pullbackTensorLax r.map
            ((CanonicalTwists.family FA hFA).obj n)
            ((CanonicalTwists.family FA hFA).obj m) ≫
          (Modules.pullback r.map).map ((CanonicalTwists.family FA hFA).mul n m) ≫
            r.theta (n + m) =
          tensorHom (r.theta n) (r.theta m) ≫
            pullbackTensorLax r.domain.ι
              ((CanonicalTwists.family FB hFB).obj n)
              ((CanonicalTwists.family FB hFB).obj m) ≫
            (Modules.pullback r.domain.ι).map
              ((CanonicalTwists.family FB hFB).mul n m)

omit [𝒜.IsCommutative] [ℬ.IsCommutative] in
/-- The graded-algebra condition is precisely preservation of the canonical
unit and every homogeneous multiplication. -/
theorem isGradedAlgebraMap_iff
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ)
    : IsGradedAlgebraMap r ↔
    (Modules.structureModulePullbackInv r.map ≫
          (Modules.pullback r.map).map (CanonicalTwists.family FA hFA).unit ≫
            r.theta 0 =
        Modules.structureModulePullbackInv r.domain.ι ≫
          (Modules.pullback r.domain.ι).map (CanonicalTwists.family FB hFB).unit) ∧
      ∀ n m : ℤ,
        pullbackTensorLax r.map
            ((CanonicalTwists.family FA hFA).obj n)
            ((CanonicalTwists.family FA hFA).obj m) ≫
          (Modules.pullback r.map).map ((CanonicalTwists.family FA hFA).mul n m) ≫
            r.theta (n + m) =
          tensorHom (r.theta n) (r.theta m) ≫
            pullbackTensorLax r.domain.ι
              ((CanonicalTwists.family FB hFB).obj n)
              ((CanonicalTwists.family FB hFB).obj m) ≫
            (Modules.pullback r.domain.ι).map
              ((CanonicalTwists.family FB hFB).mul n m) :=
  Iff.rfl

/-- The degreewise comparison `θ_ψ` of a triple characterized by étale localization
is a map of `ℤ`-graded algebras: it preserves the unit and homogeneous
multiplication of the canonical Serre twists. -/
theorem theta_isGradedAlgebraMap
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    (hcompat :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g)) :
    (Modules.structureModulePullbackInv r.map ≫
          (Modules.pullback r.map).map (CanonicalTwists.family FA hFA).unit ≫
            r.theta 0 =
        Modules.structureModulePullbackInv r.domain.ι ≫
          (Modules.pullback r.domain.ι).map (CanonicalTwists.family FB hFB).unit) ∧
      ∀ n m : ℤ,
        pullbackTensorLax r.map
            ((CanonicalTwists.family FA hFA).obj n)
            ((CanonicalTwists.family FA hFA).obj m) ≫
          (Modules.pullback r.map).map ((CanonicalTwists.family FA hFA).mul n m) ≫
            r.theta (n + m) =
          tensorHom (r.theta n) (r.theta m) ≫
            pullbackTensorLax r.domain.ι
              ((CanonicalTwists.family FB hFB).obj n)
              ((CanonicalTwists.family FB hFB).obj m) ≫
            (Modules.pullback r.domain.ι).map
              ((CanonicalTwists.family FB hFB).mul n m) :=
  sorry

/-- A graded algebra map induces a partial relative-Proj map preserving the
canonical twist-algebra operations, characterized up to a unique compatible
domain isomorphism by agreement with the scheme construction on every étale scheme. -/
theorem exists_of_etale
    (FA : ProjFunctor X 𝒜) (hFA : FA.IsAssociatedToQuadruples degA)
    (FB : ProjFunctor X ℬ) (hFB : FB.IsAssociatedToQuadruples degB)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ) :
    ∃ r : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
        𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ,
      (∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g)) ∧
      IsGradedAlgebraMap r ∧
      ∀ r', (∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r' g)) → Equivalent r' r :=
  sorry

/-- Two relative projective-spectrum maps that both satisfy the étale compatibility
condition for all étale schemes over `X` have a unique domain isomorphism
preserving their inclusions, morphisms, and comparisons. -/
theorem equivalent_of_etale
    {FA : ProjFunctor X 𝒜} {hFA : FA.IsAssociatedToQuadruples degA}
    {FB : ProjFunctor X ℬ} {hFB : FB.IsAssociatedToQuadruples degB}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    {r r' : RelativeProjMap (toAlgebraicSpace_hom FA hFA) (toAlgebraicSpace_hom FB hFB)
      𝒜 ℬ (CanonicalTwists.family FA hFA).obj (CanonicalTwists.family FB hFB).obj φ}
    (hcompat :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r g))
    (hcompat' :
      ∀ (W : Over S) (g : ofOver W ⟶ X) [Etale g]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degA)]
        [AlgebraicGeometry.RelativeProjFunctor W.left (pullbackAlgebra g degB)],
        Nonempty (EtaleChartCompatibility hFA hFB r' g)) :
    Equivalent r r' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
