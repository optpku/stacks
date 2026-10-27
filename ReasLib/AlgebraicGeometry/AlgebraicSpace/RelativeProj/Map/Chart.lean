/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.EtalePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Equality

/-! # Partial relative-Proj maps and their affine-étale characterization -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
variable {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {πP : P ⟶ X} {πQ : Q ⟶ X}
variable {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}

/-- A partial morphism over the base with degreewise comparisons on a normalized open domain. -/
structure Map (p : EtalePresentation 𝒜 πP twistP) (q : EtalePresentation ℬ πQ twistQ) where
  /-- The open set in the space of points of the target relative Proj. -/
  domain : Opens (Points Q)
  /-- The morphism from the actual open subfunctor. -/
  map : OpenSubspace.Construction.space Q domain ⟶ P
  /-- The partial morphism respects the structural maps to the base. -/
  map_over_base : map ≫ πP = OpenSubspace.Construction.ι Q domain ≫ πQ
  /-- The integral-degree twist comparisons. -/
  theta : ∀ n : ℤ, (Modules.pullback map).obj (twistP n) ⟶
    (Modules.pullback (OpenSubspace.Construction.ι Q domain)).obj (twistQ n)

namespace Map
variable {p : EtalePresentation 𝒜 πP twistP} {q : EtalePresentation ℬ πQ twistQ}

/-- Assemble a partial map from an open, an over-base morphism, and integral twist comparisons. -/
def ofDomain (domain : Opens (Points Q))
    (f : OpenSubspace.Construction.space Q domain ⟶ P)
    (hf : f ≫ πP = OpenSubspace.Construction.ι Q domain ≫ πQ)
    (theta : ∀ n : ℤ, (Modules.pullback f).obj (twistP n) ⟶
      (Modules.pullback (OpenSubspace.Construction.ι Q domain)).obj (twistQ n)) : Map p q :=
  ⟨domain, f, hf, theta⟩

/-- The open domain, over-base equation, and comparisons of an assembled partial map. -/
theorem spec (r : Map p q) :
    r.map ≫ πP = OpenSubspace.Construction.ι Q r.domain ≫ πQ ∧
    (ofDomain r.domain r.map r.map_over_base r.theta : Map p q).domain = r.domain ∧
    (ofDomain r.domain r.map r.map_over_base r.theta : Map p q).map = r.map ∧
    ∀ n, (ofDomain r.domain r.map r.map_over_base r.theta : Map p q).theta n = r.theta n := sorry

/-- The scheme chart domain is the actual inverse image of the partial domain. -/
def chartDomain (r : Map p q) (U : affineEtaleSite X) : (q.chart U).left.Opens :=
  ⟨Points.mapOfOver (q.chartMap U) ⁻¹' r.domain,
    r.domain.isOpen.preimage ((Points.continuous_map (q.chartMap U)).comp
      (ofOver.continuous_pointsEquiv (q.chart U)))⟩

/-- The restricted projective chart as a scheme over the original base. -/
def chartOver (r : Map p q) (U : affineEtaleSite X) : Over S :=
  Over.mk ((r.chartDomain U).ι ≫ (q.chart U).hom)

/-- The actual inclusion of the inverse-image open into the projective chart. -/
def chartInclusion (r : Map p q) (U : affineEtaleSite X) : r.chartOver U ⟶ q.chart U :=
  Over.homMk (r.chartDomain U).ι rfl

/-- The restricted chart-to-target morphism. -/
def chartToTarget (r : Map p q) (U : affineEtaleSite X) : ofOver (r.chartOver U) ⟶ Q :=
  ofOverMap (r.chartInclusion U) ≫ q.chartMap U

/-- Every point of the inverse-image chart domain maps into the specified partial domain. -/
theorem chartToDomain_range (r : Map p q) (U : affineEtaleSite X) :
    Set.range (Points.map (r.chartToTarget U)) ⊆ r.domain := sorry

/-- Lift the restricted actual chart morphism into the normalized open subfunctor. -/
def chartToDomain (r : Map p q) (U : affineEtaleSite X) :
    ofOver (r.chartOver U) ⟶ OpenSubspace.Construction.space Q r.domain :=
  OpenSubspace.Construction.lift (r.chartToTarget U) (r.chartToDomain_range U)

/-- The restricted chart's projection to the affine-étale base chart. -/
def chartToBase (r : Map p q) (U : affineEtaleSite X) : r.chartOver U ⟶ U.obj.left :=
  Over.homMk ((r.chartDomain U).ι ≫ q.chartBase U) (Category.assoc _ _ _)

/-- The restricted partial morphism and the chart projection have the same map to the base. -/
theorem chartMap_over_base (r : Map p q) (U : affineEtaleSite X) :
    (r.chartToDomain U ≫ r.map) ≫ πP = ofOverMap (r.chartToBase U) ≫ U.obj.hom := sorry

/-- The chart morphism is the represented map into the fixed source projective chart. -/
def chartOverMap (r : Map p q) (U : affineEtaleSite X) : r.chartOver U ⟶ p.chart U :=
  yoneda.preimage (pullback.lift (r.chartToDomain U ≫ r.map)
    (ofOverMap (r.chartToBase U)) (r.chartMap_over_base U) ≫ (p.chartIso U).hom)

/-- The scheme morphism obtained from the actual restricted partial morphism. -/
def chartMap (r : Map p q) (U : affineEtaleSite X) :
    (r.chartDomain U).toScheme ⟶ (p.chart U).left :=
  (r.chartOverMap U).left

/-- The represented chart recovers the partial morphism, and the scheme pullback
transports of its integral twists satisfy the inverse laws. -/
theorem chartTheta_coherence (r : Map p q) (U : affineEtaleSite X) :
    ofOverMap (r.chartOverMap U) ≫ p.chartMap U = r.chartToDomain U ≫ r.map ∧
    ∀ n : ℤ,
      (p.twistCompositePullbackIso (p.chartMap U) (r.chartOverMap U) n).hom ≫
        (p.twistCompositePullbackIso (p.chartMap U) (r.chartOverMap U) n).inv = 𝟙 _ ∧
      (q.twistCompositePullbackIso (q.chartMap U) (r.chartInclusion U) n).hom ≫
        (q.twistCompositePullbackIso (q.chartMap U) (r.chartInclusion U) n).inv = 𝟙 _ := sorry

/-- Restrict the actual twist comparison and identify both ends with scheme Serre twists. -/
def chartTheta (r : Map p q) (U : affineEtaleSite X) (n : ℤ) :
    (Scheme.Modules.pullback (r.chartMap U)).obj
      (p.serreTwist U n) ⟶
    (Scheme.Modules.pullback (r.chartDomain U).ι).obj
      (q.serreTwist U n) :=
  (Scheme.Modules.pullback (r.chartMap U)).map (p.twistIso U n).inv ≫
    (p.twistCompositePullbackIso (p.chartMap U) (r.chartOverMap U) n).hom ≫
    (Modules.restrictToScheme (r.chartOver U)).map
      ((Modules.pullbackCongr (r.chartTheta_coherence U).1).hom.app (twistP n) ≫
        (Modules.pullbackCompIso (r.chartToDomain U) r.map).inv.app (twistP n) ≫
        (Modules.pullback (r.chartToDomain U)).map (r.theta n) ≫
        (Modules.pullbackCompIso (r.chartToDomain U)
          (OpenSubspace.Construction.ι Q r.domain)).hom.app (twistQ n) ≫
        (Modules.pullbackCongr (OpenSubspace.Construction.lift_ι
          (r.chartToTarget U) (r.chartToDomain_range U))).hom.app (twistQ n)) ≫
    (q.twistCompositePullbackIso (q.chartMap U) (r.chartInclusion U) n).inv ≫
    (Scheme.Modules.pullback (r.chartDomain U).ι).map (q.twistIso U n).hom

/-- The natural chart domain of a sheaf-algebra map, with the fixed section-model gradings. -/
def naturalDomain (p : EtalePresentation 𝒜 πP twistP) (q : EtalePresentation ℬ πQ twistQ)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (U : affineEtaleSite X) : (q.chart U).left.Opens :=
  @projMapDomain _ _ _ _ _ _ _ _ _ _ _ _ (p.graded U) (q.graded U) (p.hom q φ U)

/-- The natural scheme chart morphism is induced by homogeneous localization. -/
def naturalMap (p : EtalePresentation 𝒜 πP twistP) (q : EtalePresentation ℬ πQ twistQ)
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (U : affineEtaleSite X) : (naturalDomain p q φ U).toScheme ⟶
      (p.chart U).left :=
  @projMapMap _ _ _ _ _ _ _ _ _ _ _ _ (p.graded U) (q.graded U) (p.hom q φ U)

/-- Transport of equal chart opens is the canonical scheme restriction isomorphism. -/
def chartDomainIso (r : Map p q) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (U : affineEtaleSite X) (h : r.chartDomain U = naturalDomain p q φ U) :
    (r.chartDomain U).toScheme ≅ (naturalDomain p q φ U).toScheme :=
  (q.chart U).left.isoOfEq h

/-- The fraction-induced scheme twist map, transported to the supplied chart domain. -/
def naturalTheta (r : Map p q) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (U : affineEtaleSite X) (h : r.chartDomain U = naturalDomain p q φ U) (n : ℤ) :
    (Scheme.Modules.pullback ((r.chartDomainIso φ U h).hom ≫ naturalMap p q φ U)).obj
      (p.serreTwist U n) ⟶
    (Scheme.Modules.pullback (r.chartDomain U).ι).obj
      (q.serreTwist U n) :=
  (Scheme.Modules.pullbackComp (r.chartDomainIso φ U h).hom (naturalMap p q φ U)).inv.app _ ≫
    (Scheme.Modules.pullback (r.chartDomainIso φ U h).hom).map
      (@Proj.AssociatedModule.GradedMap.partialHom (p.ring U) (q.ring U)
        inferInstance inferInstance (p.grading U) (q.grading U) (p.graded U) (q.graded U)
        (p.hom q φ U) n) ≫
    (Scheme.Modules.pullbackComp (r.chartDomainIso φ U h).hom (naturalDomain p q φ U).ι).hom.app _ ≫
    (Scheme.Modules.pullbackCongr ((q.chart U).left.isoOfEq_hom_ι h)).hom.app _

/-- Equality transport of the actual chart comparison along a chart-morphism equation. -/
def chartThetaTransport (r : Map p q) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (U : affineEtaleSite X) (h : r.chartDomain U = naturalDomain p q φ U)
    (hm : r.chartMap U = (r.chartDomainIso φ U h).hom ≫ naturalMap p q φ U) (n : ℤ) :
    (Scheme.Modules.pullback ((r.chartDomainIso φ U h).hom ≫ naturalMap p q φ U)).obj
      (p.serreTwist U n) ⟶
    (Scheme.Modules.pullback (r.chartDomain U).ι).obj
      (q.serreTwist U n) :=
  (Scheme.Modules.pullbackCongr hm).inv.app _ ≫ r.chartTheta U n

/-- A partial map is canonical when every affine-étale chart has the natural domain,
homogeneous-localization morphism, and fraction-induced comparisons in all integral degrees. -/
def IsCanonical (r : Map p q) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ) : Prop :=
  ∀ U : affineEtaleSite X, ∃ h : r.chartDomain U = naturalDomain p q φ U,
    ∃ hm : r.chartMap U = (r.chartDomainIso φ U h).hom ≫ naturalMap p q φ U,
      ∀ n : ℤ, r.chartThetaTransport φ U h hm n = r.naturalTheta φ U h n

/-- Canonicality is exactly the simultaneous domain, morphism, and integral twist chart formulas. -/
theorem isCanonical_iff (r : Map p q) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ) :
    r.IsCanonical φ ↔ ∀ U : affineEtaleSite X,
      ∃ h : r.chartDomain U = naturalDomain p q φ U,
        ∃ hm : r.chartMap U = (r.chartDomainIso φ U h).hom ≫ naturalMap p q φ U,
          ∀ n : ℤ, r.chartThetaTransport φ U h hm n = r.naturalTheta φ U h n := sorry

/-- Canonical partial maps for the same graded sheaf-algebra homomorphism are equal. -/
theorem eq_of_isCanonical (r s : Map p q) (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (hr : r.IsCanonical φ) (hs : s.IsCanonical φ) : r = s := sorry

end Map
end AlgebraicGeometry.AlgebraicSpace.RelativeProj
