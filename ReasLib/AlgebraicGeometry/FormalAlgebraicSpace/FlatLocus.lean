/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.NoetherianAtlas
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.FormalSpectrum.CompleteDVR
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AlgebraMap
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.FormalSpace.AdicBaseMap
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.IdealPower.TorsionIdeal
public import ReasLib.RingTheory.Completion.LocalRing

/-!
# Flat locus of a locally Noetherian formal algebraic space over a complete DVR

On each Noetherian affine étale chart `U`, presented by an adic Noetherian
ring `B` with ideal of definition `I`, the closed formal subspace is the sheafy
`Spf` of `B' := B ⧸ π-power torsion`, with ideal of definition the image of
`I`. Equivalently it is the subfunctor of `U` of sections that fppf-locally
factor through `Spec(B / (t + I^{n+1}))`, where `t ⊂ B` is `m_A`-power torsion
for the continuous `A`-algebra structure induced by `U ⟶ X ⟶ spf A`. These
immersions are glued as the fppf sheaf image of their coproduct in `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open IsLocalRing Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Forget the local nilpotence condition on a formal-spectrum section. The
underlying over-S morphism is preserved exactly. -/
def spfForget {S : Scheme.{u}} (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A] (hA : Spec (.of A) ⟶ S) :
    spf A hA ⟶ yoneda.obj (Over.mk hA) where
  app _ := ofHom Subtype.val
  naturality _ _ _ := rfl

/-- The actual presentation morphism to the representable spectrum of the base. -/
def presentationToBase {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) :
    (presentationCocone U).pt ⟶ yoneda.obj (Over.mk hA) :=
  presentationCoconeι U ≫ π ≫ p ≫ spfForget A hA

/-- The Yoneda stage of a presentation composed with a morphism into `spf A`. -/
def presentationStageToSpf {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    yoneda.obj ((presentationDiagram U).obj n) ⟶ spf A hA :=
  (presentationCocone U).ι.app n ≫ presentationCoconeι U ≫ π ≫ p

/-- The Over-morphism `D.obj n ⟶ Spec(A)` extracted from the presentation
cocone morphism to `spf A`. -/
def presentationStageOverHom {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    (presentationDiagram U).obj n ⟶ Over.mk hA :=
  AdicPresentation.stageToBase (chartStructureHom U) (chartIdeal U)
    (presentationCocone U) (presentationToBase π p) n

/-- The recovered stage morphism is the original chart morphism, after forgetting
the formal-spectrum membership proof. -/
theorem presentationStageOverHom_spec {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    yoneda.map (presentationStageOverHom π p n) =
      presentationStageToSpf π p n ≫ spfForget A hA :=
  AdicPresentation.stageToBase_yoneda (chartStructureHom U) (chartIdeal U)
    (presentationCocone U) (presentationToBase π p) n

/-- The ring homomorphism `A →+* Γ(D.obj n)` of the stage morphism
`D.obj n ⟶ spf A hA` read from the presentation cocone. -/
def chartStageAlgebraMap {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    A →+* Γ(((presentationDiagram U).obj n).left, ⊤) :=
  CommRingCat.Hom.hom <|
    (Scheme.ΓSpecIso (.of A)).inv ≫ (presentationStageOverHom π p n).left.appTop

/-- `chartStageAlgebraMap π p n` is the global-sections homomorphism of the
stage morphism `D.obj n ⟶ spf A hA`. -/
theorem chartStageAlgebraMap_spec {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    CommRingCat.ofHom (chartStageAlgebraMap π p n) =
      (Scheme.ΓSpecIso (.of A)).inv ≫
        (presentationStageOverHom π p n).left.appTop :=
  sorry

/-- The actual stage homomorphism, recovered by the proved Spec equivalence. -/
def chartStageQuotMap {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    A →+* chartRing U ⧸ chartIdeal U ^ (n + 1) :=
  AdicPresentation.stageRingHom (chartStructureHom U) (chartIdeal U)
    (presentationCocone U) (presentationToBase π p) n

/-- The compatible family `A →+* chartRing U ⧸ chartIdeal U ^ n` induced by
`U ⟶ X ⟶ spf A hA`. -/
def chartStageFamily {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    A →+* chartRing U ⧸ chartIdeal U ^ n :=
  AdicPresentation.stageFamily (chartStructureHom U) (chartIdeal U)
    (presentationCocone U) (presentationToBase π p) n

/-- The family `chartStageFamily` is compatible with the adic transition maps. -/
theorem chartStageFamily_compatible {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (chartIdeal U) hle).comp (chartStageFamily π p n) =
      chartStageFamily π p m :=
  AdicPresentation.stageFamily_compatible (chartStructureHom U) (chartIdeal U)
    (presentationCocone U) (presentationToBase π p) hle

/-- The actual homomorphism into the complete presenting ring, recovered from
its compatible quotient stages using the Γ/Spec adjunction. -/
def chartAlgebraMap {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) :
    A →+* chartRing U :=
  AdicPresentation.structureMap (chartStructureHom U) (chartIdeal U)
    (presentationCocone U) (presentationToBase π p)

/-- The recovered ring map has exactly the original morphism on every quotient stage. -/
theorem chartAlgebraMap_spec {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    (Ideal.Quotient.mk (chartIdeal U ^ (n + 1))).comp (chartAlgebraMap π p) =
      chartStageQuotMap π p n :=
  AdicPresentation.structureMap_mod (chartStructureHom U) (chartIdeal U)
    (presentationCocone U) (presentationToBase π p) n

/-- The recovered ring map induces exactly the original over-S morphism at every stage. -/
theorem chartAlgebraMap_geometric_spec {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartIdeal U ^ (n + 1)))) ≫
        Spec.map (CommRingCat.ofHom (chartAlgebraMap π p)) =
      (presentationStageOverHom π p n).left :=
  AdicPresentation.structureMap_stage (chartStructureHom U) (chartIdeal U)
    (presentationCocone U) (presentationToBase π p) n

/-- A map from an affine stage to `Spf(A)` kills a power of the maximal ideal. -/
theorem chartStageQuotMap_kills_base_power {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    ∃ k, maximalIdeal A ^ k ≤ RingHom.ker (chartStageQuotMap π p n) :=
  sorry

/-- The recovered structure map is continuous for the adic topologies of the
base discrete valuation ring and the complete presenting ring. -/
theorem chartAlgebraMap_continuous {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (hAdic : IsAdic (maximalIdeal A))
    {hA : Spec (.of A) ⟶ S} {X U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) : Continuous (chartAlgebraMap π p) :=
  AdicPresentation.structureMap_continuous (chartStructureHom U) (chartIdeal U)
    (presentationCocone U) (presentationToBase π p) (maximalIdeal A) hAdic
    (chartIdeal_properties U).1 (chartStageQuotMap_kills_base_power π p)

/-- The actual base-power-torsion ideal in the complete presenting ring. -/
def chartTorsionIdeal {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) : Ideal (chartRing U) :=
  Ideal.powerTorsionIdeal ((maximalIdeal A).map (chartAlgebraMap π p))

/-- Membership is uniform annihilation by one power of the actual base ideal. -/
theorem mem_chartTorsionIdeal {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) {x : chartRing U} :
    x ∈ chartTorsionIdeal π p ↔
      ∃ n : ℕ, ((maximalIdeal A).map (chartAlgebraMap π p)) ^ n ≤
        Ideal.torsionOf (chartRing U) (chartRing U) x :=
  Iff.rfl

/-- The π-power-torsion quotient of the presenting adic ring of a chart. -/
abbrev chartQuotRing {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) : Type u :=
  chartRing U ⧸ chartTorsionIdeal π p

/-- `chartQuotRing` is the quotient of `chartRing U` by `chartTorsionIdeal`. -/
theorem chartQuotRing_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) :
    chartQuotRing π p = (chartRing U ⧸ chartTorsionIdeal π p) :=
  sorry

/-- The structure morphism of `Spec(chartRing U ⧸ chartTorsionIdeal π p)`. -/
def chartQuotStructureHom {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) :
    Spec (.of (chartRing U ⧸ chartTorsionIdeal π p)) ⟶ S :=
  Spec.map
      (CommRingCat.ofHom
        (algebraMap (chartRing U) (chartRing U ⧸ chartTorsionIdeal π p))) ≫
    chartStructureHom U

/-- The image of the ideal of definition in the π-power-torsion quotient. -/
def chartQuotIdeal {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) :
    Ideal (chartRing U ⧸ chartTorsionIdeal π p) :=
  (chartIdeal U).map
    (algebraMap (chartRing U) (chartRing U ⧸ chartTorsionIdeal π p))

/-- The sheafy formal spectrum of `chartRing U ⧸ π-power torsion`, with ideal of
definition the image of `chartIdeal U`. -/
def affineFlatLocus {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) : (Over S)ᵒᵖ ⥤ Type u :=
  completionAlongSubspace
    (AffineFormalAlgebraicSpace.closedImmersion (chartQuotStructureHom π p)
      (chartQuotIdeal π p))

/-- `affineFlatLocus` is the completion of `Spec(B ⧸ t)` along the image of the
ideal of definition. -/
theorem affineFlatLocus_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) :
    affineFlatLocus π p =
      completionAlongSubspace
        (AffineFormalAlgebraicSpace.closedImmersion (chartQuotStructureHom π p)
          (chartQuotIdeal π p)) :=
  sorry

/-- The closed immersion `Spf(B ⧸ t) ⟶ Spf(B)` induced by the quotient map of
the presenting adic ring. -/
def affineFlatLocusι {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) :
    affineFlatLocus π p ⟶
      completionAlongSubspace
        (AffineFormalAlgebraicSpace.closedImmersion (chartStructureHom U)
          (chartIdeal U)) :=
  AffineFormalAlgebraicSpace.spfAdicCompletionMap
    (chartRing U ⧸ chartTorsionIdeal π p) (chartStructureHom U) (chartIdeal U)

/-- `affineFlatLocusι` is `spfAdicCompletionMap` of the quotient map
`chartRing U →+* chartRing U ⧸ chartTorsionIdeal π p`. -/
theorem affineFlatLocusι_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) :
    affineFlatLocusι π p =
      AffineFormalAlgebraicSpace.spfAdicCompletionMap
        (chartRing U ⧸ chartTorsionIdeal π p) (chartStructureHom U)
        (chartIdeal U) :=
  sorry

/-- The closed immersion of `affineFlatLocus` into the sheafy `Spf` of the
presenting adic ring. -/
instance instClosedImmersion_affineFlatLocusι {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsCompleteLocalRing A] {hA : Spec (.of A) ⟶ S}
    {X : (Over S)ᵒᵖ ⥤ Type u} {U : (Over S)ᵒᵖ ⥤ Type u}
    [IsNoetherianAffine U] (π : U ⟶ X) (p : X ⟶ spf A hA) :
    ClosedImmersion (affineFlatLocusι π p) :=
  sorry

/-- The `n`th infinitesimal stage of `Spf(B ⧸ t)`, as
`Spec(chartRing U ⧸ (chartTorsionIdeal ⊔ chartIdeal U ^ (n + 1)))`. -/
def chartTorsionStage {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) : Over S :=
  Over.mk
    (Spec.map
        (CommRingCat.ofHom
          (Ideal.Quotient.factor
            (le_sup_right :
              chartIdeal U ^ (n + 1) ≤
                chartTorsionIdeal π p ⊔ chartIdeal U ^ (n + 1)))) ≫
      (presentationStageIso U n).inv ≫ ((presentationDiagram U).obj n).hom)

/-- The closed immersion of a `B ⧸ t` power stage into the corresponding
presentation stage of `U`. -/
def chartTorsionStageToChart {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    chartTorsionStage π p n ⟶ (presentationDiagram U).obj n :=
  Over.homMk
    (Spec.map
        (CommRingCat.ofHom
          (Ideal.Quotient.factor
            (le_sup_right :
              chartIdeal U ^ (n + 1) ≤
                chartTorsionIdeal π p ⊔ chartIdeal U ^ (n + 1)))) ≫
      (presentationStageIso U n).inv)
    sorry

/-- The comparison from a `B ⧸ t` power stage into the Noetherian affine chart. -/
def chartTorsionStageι {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (n : ℕ) :
    yoneda.obj (chartTorsionStage π p n) ⟶ U :=
  yoneda.map (chartTorsionStageToChart π p n) ≫
    (presentationCocone U).ι.app n ≫ presentationCoconeι U

/-- A Yoneda section of a Noetherian affine chart fppf-locally factors through
a power stage of `B ⧸ π-power torsion`. -/
def IsChartFlatSection {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) {T : (Over S)ᵒᵖ} (x : U.obj T) : Prop :=
  ∃ (ι : Type u) (cover : ι → Over S) (πs : (i : ι) → cover i ⟶ T.unop),
    Sieve.ofArrows cover πs ∈ Scheme.fppfTopology.over S T.unop ∧
      ∀ i, ∃ (n : ℕ) (y : (yoneda.obj (chartTorsionStage π p n)).obj (op (cover i))),
        (chartTorsionStageι π p n).app (op (cover i)) y = U.map (πs i).op x

/-- A chart section belongs to the flat subfunctor exactly when it locally
factors through a torsion quotient stage. -/
theorem IsChartFlatSection.iff {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) {T : (Over S)ᵒᵖ} (x : U.obj T) :
    IsChartFlatSection π p x ↔
      ∃ (ι : Type u) (cover : ι → Over S) (πs : (i : ι) → cover i ⟶ T.unop),
        Sieve.ofArrows cover πs ∈ Scheme.fppfTopology.over S T.unop ∧
          ∀ i, ∃ (n : ℕ) (y : (yoneda.obj (chartTorsionStage π p n)).obj (op (cover i))),
            (chartTorsionStageι π p n).app (op (cover i)) y = U.map (πs i).op x :=
  sorry

/-- Local factoring through π-torsion stages is stable under restriction. -/
theorem IsChartFlatSection.map {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) {T₁ T₂ : (Over S)ᵒᵖ} (f : T₁ ⟶ T₂)
    {x : U.obj T₁} (hx : IsChartFlatSection π p x) :
    IsChartFlatSection π p (U.map f x) :=
  sorry

/-- The sheafy `Spf` of `B ⧸ π-power torsion` as a subfunctor of a Noetherian
affine chart: sections that fppf-locally factor through
`Spec(B / (t ⊔ I^{n+1}))`. -/
def ofNoetherianAffine {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := { x : U.obj T // IsChartFlatSection π p x }
  map f := ofHom fun x ↦ ⟨U.map f x.1, IsChartFlatSection.map π p f x.2⟩
  map_id := sorry
  map_comp := sorry

/-- Sections of `ofNoetherianAffine π p` are sections of the chart that
fppf-locally factor through a π-torsion presentation stage. -/
theorem ofNoetherianAffine_obj {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (T : (Over S)ᵒᵖ) :
    (ofNoetherianAffine π p).obj T = { x : U.obj T // IsChartFlatSection π p x } :=
  sorry

/-- The closed immersion of the π-torsion formal spectrum of a Noetherian
affine chart into the chart. -/
def ofNoetherianAffineι {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) : ofNoetherianAffine π p ⟶ U where
  app _ := ofHom fun x ↦ x.1
  naturality := sorry

/-- Components of `ofNoetherianAffineι` are the subtype projections. -/
theorem ofNoetherianAffineι_app {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) (T : (Over S)ᵒᵖ) :
    (ofNoetherianAffineι π p).app T = ofHom fun x ↦ x.1 :=
  sorry

/-- A section of a Noetherian affine chart lies in the image of
`ofNoetherianAffineι` if and only if it is a chartwise flat-locus section. -/
theorem mem_ofNoetherianAffine {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsNoetherianAffine U]
    (π : U ⟶ X) (p : X ⟶ spf A hA) {T : (Over S)ᵒᵖ} (x : U.obj T) :
    (∃ y, (ofNoetherianAffineι π p).app T y = x) ↔ IsChartFlatSection π p x :=
  sorry

/-- The sheafy π-torsion locus of a Noetherian affine chart is a formal
algebraic space. -/
instance instIsFormalAlgebraicSpace_ofNoetherianAffine {S : Scheme.{u}}
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsCompleteLocalRing A] {hA : Spec (.of A) ⟶ S}
    {X : (Over S)ᵒᵖ ⥤ Type u} {U : (Over S)ᵒᵖ ⥤ Type u}
    [IsNoetherianAffine U] (π : U ⟶ X) (p : X ⟶ spf A hA) :
    IsFormalAlgebraicSpace (ofNoetherianAffine π p) :=
  sorry

/-- The sheafy π-torsion locus of a Noetherian affine chart is locally
Noetherian. -/
instance instIsLocallyNoetherian_ofNoetherianAffine {S : Scheme.{u}}
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsCompleteLocalRing A] {hA : Spec (.of A) ⟶ S}
    {X : (Over S)ᵒᵖ ⥤ Type u} {U : (Over S)ᵒᵖ ⥤ Type u}
    [IsNoetherianAffine U] (π : U ⟶ X) (p : X ⟶ spf A hA) :
    IsLocallyNoetherian (ofNoetherianAffine π p) :=
  sorry

/-- The comparison from the π-torsion locus of a Noetherian affine chart into
the chart is a closed immersion. -/
instance instClosedImmersion_ofNoetherianAffineι {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsCompleteLocalRing A] {hA : Spec (.of A) ⟶ S}
    {X : (Over S)ᵒᵖ ⥤ Type u} {U : (Over S)ᵒᵖ ⥤ Type u}
    [IsNoetherianAffine U] (π : U ⟶ X) (p : X ⟶ spf A hA) :
    ClosedImmersion (ofNoetherianAffineι π p) :=
  sorry

/-- The family of sheafy π-torsion loci of the chosen Noetherian étale atlas. -/
def atlasLocus {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) (i : atlasIndex X) : (Over S)ᵒᵖ ⥤ Type u :=
  ofNoetherianAffine (atlasπ X i) p

/-- `atlasLocus p i` is the sheafy π-torsion formal spectrum of the `i`th
atlas chart. -/
theorem atlasLocus_eq {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) (i : atlasIndex X) :
    atlasLocus p i = ofNoetherianAffine (atlasπ X i) p :=
  sorry

/-- The coproduct of sheafy π-torsion loci of a locally Noetherian étale
atlas. -/
def atlasLocusCoproduct {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : (Over S)ᵒᵖ ⥤ Type u :=
  sigmaFunctor fun i ↦ atlasLocus p i

/-- The copairing of the atlaswise π-torsion immersions into `X`. -/
def atlasLocusDesc {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : atlasLocusCoproduct p ⟶ X :=
  sigmaDesc fun i ↦ ofNoetherianAffineι (atlasπ X i) p ≫ atlasπ X i

/-- Components of `atlasLocusDesc` are the chartwise π-torsion immersions. -/
theorem atlasLocusDesc_app {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) (T : (Over S)ᵒᵖ)
    (q : (atlasLocusCoproduct p).obj T) :
    (atlasLocusDesc p).app T q =
      (ofNoetherianAffineι (atlasπ X q.1) p ≫ atlasπ X q.1).app T q.2 :=
  sorry

/-- A Yoneda section of `X` fppf-locally factors through the coproduct of
π-torsion chart loci. -/
def IsFlatLocusSection {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) {T : (Over S)ᵒᵖ} (x : X.obj T) : Prop :=
  ∃ (ι : Type u) (cover : ι → Over S) (πs : (i : ι) → cover i ⟶ T.unop),
    Sieve.ofArrows cover πs ∈ Scheme.fppfTopology.over S T.unop ∧
      ∀ i, ∃ y,
        (atlasLocusDesc p).app (op (cover i)) y = X.map (πs i).op x

/-- A section belongs to the flat locus exactly when it locally lifts to a
chartwise torsion quotient. -/
theorem IsFlatLocusSection.iff {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) {T : (Over S)ᵒᵖ} (x : X.obj T) :
    IsFlatLocusSection p x ↔
      ∃ (ι : Type u) (cover : ι → Over S) (πs : (i : ι) → cover i ⟶ T.unop),
        Sieve.ofArrows cover πs ∈ Scheme.fppfTopology.over S T.unop ∧
          ∀ i, ∃ y,
            (atlasLocusDesc p).app (op (cover i)) y = X.map (πs i).op x :=
  sorry

/-- Local factoring through π-torsion chart loci is stable under restriction. -/
theorem IsFlatLocusSection.map {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) {T₁ T₂ : (Over S)ᵒᵖ} (f : T₁ ⟶ T₂) {x : X.obj T₁}
    (hx : IsFlatLocusSection p x) :
    IsFlatLocusSection p (X.map f x) :=
  sorry

/-- The flat locus of a locally Noetherian formal algebraic space over a
complete discrete valuation ring, as the fppf sheaf of sections of `X` that
locally factor through the π-torsion quotients of an étale Noetherian affine
atlas. -/
def flatLocus {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := { x : X.obj T // IsFlatLocusSection p x }
  map f := ofHom fun x ↦ ⟨X.map f x.1, IsFlatLocusSection.map p f x.2⟩
  map_id := sorry
  map_comp := sorry

/-- Sections of `flatLocus p` over `T` are sections of `X` that fppf-locally
factor through the π-torsion chart loci. -/
theorem flatLocus_obj {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) (T : (Over S)ᵒᵖ) :
    (flatLocus p).obj T = { x : X.obj T // IsFlatLocusSection p x } :=
  sorry

/-- The canonical closed immersion from the flat locus into `X`. -/
def flatLocusι {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : flatLocus p ⟶ X where
  app _ := ofHom fun x ↦ x.1
  naturality := sorry

/-- Components of `flatLocusι p` are the subtype projections of `flatLocus p`. -/
theorem flatLocusι_app {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) (T : (Over S)ᵒᵖ) :
    (flatLocusι p).app T = ofHom fun x ↦ x.1 :=
  sorry

/-- Applying the structure morphism of `X` to a section of the flat locus is
postcomposition of the subtype projection with `p`. -/
theorem flatLocusι_comp {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) (T : (Over S)ᵒᵖ) (x : (flatLocus p).obj T) :
    p.app T ((flatLocusι p).app T x) = p.app T x.1 :=
  sorry

/-- The flat locus is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_flatLocus {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsCompleteLocalRing A] {hA : Spec (.of A) ⟶ S}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : IsFormalAlgebraicSpace (flatLocus p) :=
  sorry

/-- The flat locus is locally Noetherian. -/
instance instIsLocallyNoetherian_flatLocus {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsCompleteLocalRing A] {hA : Spec (.of A) ⟶ S}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : IsLocallyNoetherian (flatLocus p) :=
  sorry

/-- The comparison from the flat locus of a Noetherian affine chart to the
sheafy `Spf` of its π-power-torsion quotient. -/
def affine_stage_spec_hom {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {U : (Over S)ᵒᵖ ⥤ Type u}
    [IsNoetherianAffine U] (p : U ⟶ spf A hA) :
    flatLocus p ⟶ ofNoetherianAffine (𝟙 U) p where
  app T := ofHom fun x ↦ ⟨x.1, sorry⟩
  naturality := sorry

/-- The comparison from the sheafy `Spf` of the π-power-torsion quotient of a
Noetherian affine chart into its flat locus. -/
def affine_stage_spec_inv {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {U : (Over S)ᵒᵖ ⥤ Type u}
    [IsNoetherianAffine U] (p : U ⟶ spf A hA) :
    ofNoetherianAffine (𝟙 U) p ⟶ flatLocus p where
  app T := ofHom fun y ↦ ⟨y.1, sorry⟩
  naturality := sorry

/-- On a Noetherian affine chart `Spf(B) → Spf(A)`, the constructed flat locus
is the subfunctor of sections that fppf-locally factor through
`Spec(B / (t ⊔ I^{n+1}))`, equivalently the sheafy `Spf` of `B / π-power
torsion`. -/
def affine_stage_spec {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {U : (Over S)ᵒᵖ ⥤ Type u}
    [IsNoetherianAffine U] (p : U ⟶ spf A hA) :
    flatLocus p ≅ ofNoetherianAffine (𝟙 U) p where
  hom := affine_stage_spec_hom hA p
  inv := affine_stage_spec_inv hA p
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `affine_stage_spec` is the comparison isomorphism of `affine_stage_spec_hom` and
`affine_stage_spec_inv`. -/
theorem affine_stage_spec_hom_inv {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {U : (Over S)ᵒᵖ ⥤ Type u}
    [IsNoetherianAffine U] (p : U ⟶ spf A hA) :
    (affine_stage_spec hA p).hom = affine_stage_spec_hom hA p ∧
      (affine_stage_spec hA p).inv = affine_stage_spec_inv hA p :=
  sorry

/-- A Yoneda section of a locally Noetherian morphism that is flat over the
complete discrete valuation ring is a section of the flat locus. -/
theorem IsFlatLocusSection.of_flat {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) {Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace Y] [IsLocallyNoetherian Y] (g : Y ⟶ X)
    [Flat (g ≫ p)] {T : (Over S)ᵒᵖ} (y : Y.obj T) :
    IsFlatLocusSection p (g.app T y) :=
  sorry

/-- The canonical factorization of a morphism of locally Noetherian formal
algebraic spaces that is flat over the complete discrete valuation ring
through the flat locus. -/
def lift {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) {Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace Y] [IsLocallyNoetherian Y] (g : Y ⟶ X)
    [Flat (g ≫ p)] : Y ⟶ flatLocus p where
  app T := ofHom fun y ↦ ⟨g.app T y, IsFlatLocusSection.of_flat p g y⟩
  naturality := sorry

/-- Components of `lift p g` are the corresponding sections of `g`. -/
theorem lift_app {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) {Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace Y] [IsLocallyNoetherian Y] (g : Y ⟶ X)
    [Flat (g ≫ p)] (T : (Over S)ᵒᵖ) (y : Y.obj T) :
    ((lift p g).app T y).1 = g.app T y :=
  sorry

/-- Factorizations through the flat locus are unique, because the closed
immersion is a monomorphism of sheaves. -/
theorem liftUnique_flatLocus {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    {hA : Spec (.of A) ⟶ S} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) {Y : (Over S)ᵒᵖ ⥤ Type u}
    {h₁ h₂ : Y ⟶ flatLocus p} (h : h₁ ≫ flatLocusι p = h₂ ≫ flatLocusι p) :
    h₁ = h₂ :=
  sorry

/-- The inclusion of the flat locus of a locally Noetherian formal algebraic
space over a complete discrete valuation ring is a closed immersion. -/
@[stacks 0GD8, instance]
instance instClosedImmersion_flatLocusι {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : ClosedImmersion (flatLocusι p) :=
  sorry

/-- The flat locus is flat over the complete discrete valuation ring. -/
@[stacks 0GD8, instance]
instance instFlat_flatLocusToSpf {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) : Flat (flatLocusι p ≫ p) :=
  sorry

/-- Every morphism from a locally Noetherian formal algebraic space flat over
the complete discrete valuation ring factors through the flat locus. -/
@[stacks 0GD8]
theorem factorsThrough_flatLocus {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) {Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace Y] [IsLocallyNoetherian Y] (g : Y ⟶ X)
    [Flat (g ≫ p)] : lift p g ≫ flatLocusι p = g :=
  sorry

/-- The flat locus is a closed flat formal subspace through which every
morphism from a locally Noetherian formal space flat over the base factors. -/
theorem flatLocus_spec {S : Scheme.{u}} {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (p : X ⟶ spf A hA) :
    ClosedImmersion (flatLocusι p) ∧ Flat (flatLocusι p ≫ p) ∧
      (∀ {Y : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace Y]
        [IsLocallyNoetherian Y] (g : Y ⟶ X) [Flat (g ≫ p)],
        lift p g ≫ flatLocusι p = g) := by
  exact ⟨instClosedImmersion_flatLocusι hA p, instFlat_flatLocusToSpf hA p,
    fun g ↦ factorsThrough_flatLocus hA p g⟩

end AlgebraicGeometry.FormalAlgebraicSpace
