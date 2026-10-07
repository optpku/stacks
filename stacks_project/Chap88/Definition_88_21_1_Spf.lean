module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# Formal spectra of complete discrete valuation rings

The formal spectrum of a complete discrete valuation ring `R` over a scheme `S`
is the fppf sheaf associated to the Yoneda colimit of the affine thickenings
`Spec(R ⧸ m_R^{n+1})`: a `T`-point is a morphism `T ⟶ Spec(R)` over `S` that
fppf-locally factors through some infinitesimal neighbourhood of the closed
point. An extension of complete discrete valuation rings induces a morphism of
these sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The affine thickening `Spec(R ⧸ m_R^{n+1})` of a local ring, viewed as a
scheme over `S` via the structure morphism of `Spec(R)`. -/
def dvrStage (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) ≫
    structureHom)

/-- The underlying scheme of `dvrStage R n structureHom` is `Spec(R ⧸ m_R^{n+1})`. -/
theorem dvrStage_left (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    (dvrStage R n structureHom).left = Spec (.of (R ⧸ maximalIdeal R ^ (n + 1))) :=
  sorry

/-- The successor thickening `Spec(R ⧸ m_R^{n+1}) ⟶ Spec(R ⧸ m_R^{n+2})` over `S`. -/
def dvrSucc (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    dvrStage R n structureHom ⟶ dvrStage R (n + 1) structureHom :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc (maximalIdeal R) (n + 1))))
    sorry

/-- The underlying scheme morphism of `dvrSucc` is `Spec.map` of the quotient
factor map `R ⧸ m_R^{n+2} →+* R ⧸ m_R^{n+1}`. -/
theorem dvrSucc_left (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    (dvrSucc R n structureHom).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc (maximalIdeal R) (n + 1))) :=
  sorry

/-- The `ℕ`-indexed diagram of affine thickenings `Spec(R ⧸ m_R^{n+1})` over `S`. -/
def dvrThickenings (R : Type u) [CommRing R] [IsLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) : ℕ ⥤ Over S :=
  Functor.ofSequence fun n ↦ dvrSucc R n structureHom

/-- Objects of `dvrThickenings R structureHom` are the stages `dvrStage R n structureHom`. -/
theorem dvrThickenings_obj (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    (dvrThickenings R structureHom).obj n = dvrStage R n structureHom :=
  sorry

/-- Each stage `Spec(R ⧸ m_R^{n+1})` of the thickening diagram is affine. -/
instance dvrThickenings_obj_isAffine (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    IsAffine ((dvrThickenings R structureHom).obj n).left :=
  sorry

/-- Transition maps of `dvrThickenings R structureHom` are thickenings. -/
instance dvrThickenings_map_isThickening (R : Type u) [CommRing R] [IsLocalRing R]
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) {n m : ℕ} (f : n ⟶ m) :
    IsThickening ((dvrThickenings R structureHom).map f).left :=
  sorry

/-- The closed immersion `Spec(R ⧸ m_R^{n+1}) ⟶ Spec(R)` over `S`. -/
def dvrStageToSpec (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    dvrStage R n structureHom ⟶ Over.mk structureHom :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))))
    sorry

/-- The underlying scheme morphism of `dvrStageToSpec` is `Spec.map` of the
quotient map `R →+* R ⧸ m_R^{n+1}`. -/
theorem dvrStageToSpec_left (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ)
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    (dvrStageToSpec R n structureHom).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) :=
  sorry

/-- A morphism `T ⟶ Spec(R)` over `S` fppf-locally factors through some
infinitesimal neighbourhood `Spec(R ⧸ m_R^{n+1})`. -/
def fppfLocallyFactorsThroughDvrStage (R : Type u) [CommRing R] [IsLocalRing R]
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) {T : Over S}
    (f : T ⟶ Over.mk structureHom) : Prop :=
  ∃ (ι : Type u) (cover : ι → Over S) (π : (i : ι) → cover i ⟶ T),
    Sieve.ofArrows cover π ∈ Scheme.fppfTopology.over S T ∧
      ∀ i, ∃ n, ∃ g : cover i ⟶ dvrStage R n structureHom,
        g ≫ dvrStageToSpec R n structureHom = π i ≫ f

/-- Unfolding of `fppfLocallyFactorsThroughDvrStage`. -/
theorem fppfLocallyFactorsThroughDvrStage_iff (R : Type u) [CommRing R] [IsLocalRing R]
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) {T : Over S}
    (f : T ⟶ Over.mk structureHom) :
    fppfLocallyFactorsThroughDvrStage R structureHom f ↔
      ∃ (ι : Type u) (cover : ι → Over S) (π : (i : ι) → cover i ⟶ T),
        Sieve.ofArrows cover π ∈ Scheme.fppfTopology.over S T ∧
          ∀ i, ∃ n, ∃ g : cover i ⟶ dvrStage R n structureHom,
            g ≫ dvrStageToSpec R n structureHom = π i ≫ f :=
  sorry

/-- A morphism that factors through some `dvrStage` fppf-locally factors through
a discrete valuation ring thickening. -/
theorem fppfLocallyFactorsThroughDvrStage.of_stage (R : Type u) [CommRing R]
    [IsLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) {T : Over S}
    (n : ℕ) (g : T ⟶ dvrStage R n structureHom) :
    fppfLocallyFactorsThroughDvrStage R structureHom
      (g ≫ dvrStageToSpec R n structureHom) :=
  sorry

/-- Fppf-local factoring through a discrete valuation ring thickening is stable
under precomposition in `Over S`. -/
theorem fppfLocallyFactorsThroughDvrStage_map (R : Type u) [CommRing R]
    [IsLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S)
    {T₁ T₂ : (Over S)ᵒᵖ} (h : T₁ ⟶ T₂) {f : T₁.unop ⟶ Over.mk structureHom}
    (hf : fppfLocallyFactorsThroughDvrStage R structureHom f) :
    fppfLocallyFactorsThroughDvrStage R structureHom (h.unop ≫ f) :=
  sorry

/-- The Yoneda colimit of the affine thickenings of a complete discrete valuation
ring, before fppf sheafification. -/
def spfPresheaf (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type u :=
  colimit (dvrThickenings R structureHom ⋙ yoneda)

/-- `spfPresheaf R structureHom` is the Yoneda colimit of
`dvrThickenings R structureHom`. -/
theorem spfPresheaf_eq (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    spfPresheaf R structureHom = colimit (dvrThickenings R structureHom ⋙ yoneda) :=
  sorry

/-- The formal spectrum of a complete discrete valuation ring over `S`, as the
fppf sheaf of morphisms to `Spec(R)` that locally factor through some
`Spec(R ⧸ m_R^{n+1})`. -/
def spf (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T :=
    { f : T.unop ⟶ Over.mk structureHom //
      fppfLocallyFactorsThroughDvrStage R structureHom f }
  map {T₁ T₂} h :=
    TypeCat.ofHom fun f ↦
      ⟨h.unop ≫ f.val, fppfLocallyFactorsThroughDvrStage_map R structureHom h f.property⟩
  map_id := sorry
  map_comp := sorry

/-- Sections of `spf R structureHom` over `T` are morphisms `T ⟶ Spec(R)` over
`S` that fppf-locally factor through some infinitesimal neighbourhood. -/
theorem spf_obj (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S)
    (T : (Over S)ᵒᵖ) :
    (spf R structureHom).obj T =
      { f : T.unop ⟶ Over.mk structureHom //
        fppfLocallyFactorsThroughDvrStage R structureHom f } :=
  sorry

/-- The comparison from the `n`-th Yoneda thickening into the sheafy formal
spectrum. -/
def dvrStageι (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    yoneda.obj (dvrStage R n structureHom) ⟶ spf R structureHom where
  app T :=
    TypeCat.ofHom fun (g : T.unop ⟶ dvrStage R n structureHom) ↦
      ⟨g ≫ dvrStageToSpec R n structureHom,
        fppfLocallyFactorsThroughDvrStage.of_stage R structureHom n g⟩
  naturality := sorry

/-- The comparison `dvrStageι` composes a map into the `n`-th thickening with
`dvrStageToSpec`. -/
theorem dvrStageι_app (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (T : (Over S)ᵒᵖ)
    (g : T.unop ⟶ dvrStage R n structureHom) :
    ((dvrStageι R n structureHom).app T g).val = g ≫ dvrStageToSpec R n structureHom :=
  sorry

/-- The cocone of stage inclusions from the Yoneda thickening diagram into the
sheafy formal spectrum. -/
def spfCocone (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    Cocone (dvrThickenings R structureHom ⋙ yoneda) where
  pt := spf R structureHom
  ι :=
    { app := fun n ↦ dvrStageι R n structureHom
      naturality := sorry }

/-- The sheafification unit from the Yoneda colimit of thickenings to `spf`. -/
def spfPresheafToSpf (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    spfPresheaf R structureHom ⟶ spf R structureHom :=
  colimit.desc (dvrThickenings R structureHom ⋙ yoneda) (spfCocone R structureHom)

/-- The sheafification unit is the colimit descent of the stage-inclusion
cocone. -/
theorem spfPresheafToSpf_eq (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    spfPresheafToSpf R structureHom =
      colimit.desc (dvrThickenings R structureHom ⋙ yoneda) (spfCocone R structureHom) :=
  sorry

/-- The legs of `spfCocone` are the stage inclusions `dvrStageι`. -/
theorem spfCocone_ι_app (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    (spfCocone R structureHom).ι.app n = dvrStageι R n structureHom :=
  sorry

/-- The sheafification unit restricts to `dvrStageι` on each thickening. -/
theorem spfPresheafToSpf_fac (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    colimit.ι (dvrThickenings R structureHom ⋙ yoneda) n ≫
        spfPresheafToSpf R structureHom =
      dvrStageι R n structureHom :=
  sorry

/-- The sheafification unit `spfPresheafToSpf` is fppf-locally surjective. -/
instance spfPresheafToSpf_isLocallySurjective (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (spfPresheafToSpf R structureHom) :=
  sorry

/-- The sheafification unit `spfPresheafToSpf` is fppf-locally injective. -/
instance spfPresheafToSpf_isLocallyInjective (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (spfPresheafToSpf R structureHom) :=
  sorry

/-- `spf R structureHom` is the fppf sheaf associated to the Yoneda colimit of
`dvrThickenings R structureHom`. -/
theorem spf_eq (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (spfPresheafToSpf R structureHom) ∧
      Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
        (spfPresheafToSpf R structureHom) :=
  sorry

/-- `spf R structureHom` is a sheaf for the big fppf topology on `Over S`. -/
theorem spf_isSheaf (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (spf R structureHom) :=
  sorry

/-- The thickening diagram of a complete discrete valuation ring is a directed
affine thickening colimit of its formal spectrum. -/
instance instIsDirectedAffineThickeningColimit_spf (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    IsDirectedAffineThickeningColimit (dvrThickenings R structureHom) (spf R structureHom) :=
  sorry

/-- The formal spectrum of a complete discrete valuation ring is a formal
algebraic space. -/
instance instSpf (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    IsFormalAlgebraicSpace (spf R structureHom) :=
  sorry

/-- The formal spectrum of a complete discrete valuation ring is a Noetherian
affine formal algebraic space. -/
instance instSpf_isNoetherianAffine (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    IsNoetherianAffine (spf R structureHom) :=
  sorry

/-- The formal spectrum of a complete discrete valuation ring is locally
Noetherian. -/
instance instSpf_isLocallyNoetherian (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    IsLocallyNoetherian (spf R structureHom) :=
  sorry

/-- Powers of the maximal ideal of a local homomorphism pull back along the
algebra map. -/
theorem le_comap_maximalIdeal_pow {R R' : Type u} [CommRing R] [IsLocalRing R] [CommRing R']
    [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] (n : ℕ) :
    maximalIdeal R ^ n ≤ (maximalIdeal R' ^ n).comap (algebraMap R R') :=
  Ideal.map_le_iff_le_comap.mp <|
    le_trans
      (le_of_eq (map_pow (Ideal.mapHom (algebraMap R R')) (maximalIdeal R) n))
      (pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le (algebraMap R R')) n)

/-- The morphism of affine thickenings induced by a local homomorphism of local
rings, at a fixed infinitesimal order. -/
def dvrStageMap (R R' : Type u) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    [Algebra R R'] [IsLocalHom (algebraMap R R')] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    dvrStage R' n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) ⟶
      dvrStage R n structureHom :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (maximalIdeal R' ^ (n + 1)) (algebraMap R R')
        (le_comap_maximalIdeal_pow (n + 1)))))
    sorry

/-- The morphism of thickening diagrams induced by a local homomorphism of local
rings. -/
def dvrThickeningsMap (R R' : Type u) [CommRing R] [IsLocalRing R] [CommRing R']
    [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    dvrThickenings R' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) ⟶
      dvrThickenings R structureHom :=
  NatTrans.ofSequence (fun n ↦ dvrStageMap R R' n structureHom) sorry

/-- The morphism `Spec(R') ⟶ Spec(R)` over `S` induced by an algebra map. -/
def specOverMap (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) ⟶
      Over.mk structureHom :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R R'))) sorry

/-- The underlying scheme morphism of `specOverMap` is `Spec.map` of the algebra
map. -/
theorem specOverMap_left (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    (specOverMap R R' structureHom).left =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) :=
  sorry

/-- Fppf-local factoring through thickenings of `R'` implies the same after
composition with `specOverMap`. -/
theorem fppfLocallyFactorsThroughDvrStage_comp_specOverMap (R R' : Type u)
    [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) {T : Over S}
    {f : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom)}
    (hf : fppfLocallyFactorsThroughDvrStage R'
      (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) f) :
    fppfLocallyFactorsThroughDvrStage R structureHom (f ≫ specOverMap R R' structureHom) :=
  sorry

/-- The morphism `Spf(R') ⟶ Spf(R)` induced by an extension of complete discrete
valuation rings, over the structure morphism of `Spec(R)`. -/
def spfMap (R R' : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [IsCompleteLocalRing R'] [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    spf R' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) ⟶
      spf R structureHom where
  app T :=
    TypeCat.ofHom fun f ↦
      ⟨f.val ≫ specOverMap R R' structureHom,
        fppfLocallyFactorsThroughDvrStage_comp_specOverMap R R' structureHom f.property⟩
  naturality := sorry

/-- `spfMap` is induced on sections by postcomposition with `specOverMap`. -/
theorem spfMap_app (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [IsCompleteLocalRing R'] [Algebra R R']
    [IsExtensionOfDiscreteValuationRings R R'] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (T : (Over S)ᵒᵖ)
    (f : (spf R' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom)).obj T) :
    ((spfMap R R' structureHom).app T f).val = f.val ≫ specOverMap R R' structureHom :=
  sorry

/-- Stage inclusions intertwine `spfMap` with the algebra-map thickenings. -/
theorem dvrStageι_comp_spfMap (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [IsCompleteLocalRing R'] [Algebra R R']
    [IsExtensionOfDiscreteValuationRings R R'] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    dvrStageι R' n (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) ≫
        spfMap R R' structureHom =
      yoneda.map (dvrStageMap R R' n structureHom) ≫ dvrStageι R n structureHom :=
  sorry

/-- The identity extension of a complete discrete valuation ring induces the
identity on formal spectra. -/
theorem specMap_algebraMap_id (R : Type u) [CommRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    Spec.map (CommRingCat.ofHom (algebraMap R R)) ≫ structureHom = structureHom :=
  sorry

/-- The identity extension of a complete discrete valuation ring induces the
identity on formal spectra, after identifying the structure morphisms. -/
theorem spfMap_id (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    spfMap R R structureHom =
      eqToHom (congrArg (spf R) (specMap_algebraMap_id R structureHom)) :=
  sorry

/-- Formal-spectrum maps induced by a tower of complete discrete valuation ring
extensions compose. -/
theorem specMap_algebraMap_comp (R R' R'' : Type u) [CommRing R] [CommRing R'] [CommRing R'']
    [Algebra R R'] [Algebra R' R''] [Algebra R R''] [IsScalarTower R R' R''] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    Spec.map (CommRingCat.ofHom (algebraMap R R'')) ≫ structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap R' R'')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom :=
  sorry

/-- Formal-spectrum maps induced by a tower of complete discrete valuation ring
extensions compose, after identifying the structure morphisms. -/
theorem spfMap_comp (R R' R'' : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [IsCompleteLocalRing R'] [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R'']
    [IsCompleteLocalRing R''] [Algebra R R'] [Algebra R' R''] [Algebra R R'']
    [IsScalarTower R R' R''] [IsExtensionOfDiscreteValuationRings R R']
    [IsExtensionOfDiscreteValuationRings R' R'']
    [IsExtensionOfDiscreteValuationRings R R''] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    spfMap R R'' structureHom =
      eqToHom (congrArg (spf R'') (specMap_algebraMap_comp R R' R'' structureHom)) ≫
        spfMap R' R'' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) ≫
          spfMap R R' structureHom :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
