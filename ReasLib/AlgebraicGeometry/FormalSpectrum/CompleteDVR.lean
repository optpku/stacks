module

public import Mathlib.AlgebraicGeometry.AffineScheme
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
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.FormalSpectrum.PowerStages

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
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism `T ⟶ Spec(R)` over `S` fppf-locally factors through some
infinitesimal neighbourhood `Spec(R ⧸ m_R^{n+1})`. -/
def fppfLocallyFactorsThroughDvrStage (R : Type u) [CommRing R] [IsLocalRing R]
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) {T : Over S}
    (f : T ⟶ Over.mk structureHom) : Prop :=
  ∃ (ι : Type u) (cover : ι → Over S) (π : (i : ι) → cover i ⟶ T),
    Sieve.ofArrows cover π ∈ Scheme.fppfTopology.over S T ∧
      ∀ i, ∃ n, ∃ g : cover i ⟶ powerStage structureHom (maximalIdeal R) n,
        g ≫ powerStageToSpec structureHom (maximalIdeal R) n = π i ≫ f

/-- A morphism locally factors through a maximal-ideal power stage precisely when it
admits an fppf covering on which such factorizations exist. -/
theorem fppfLocallyFactorsThroughDvrStage_iff (R : Type u) [CommRing R] [IsLocalRing R]
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) {T : Over S}
    (f : T ⟶ Over.mk structureHom) :
    fppfLocallyFactorsThroughDvrStage R structureHom f ↔
      ∃ (ι : Type u) (cover : ι → Over S) (π : (i : ι) → cover i ⟶ T),
        Sieve.ofArrows cover π ∈ Scheme.fppfTopology.over S T ∧
          ∀ i, ∃ n, ∃ g : cover i ⟶ powerStage structureHom (maximalIdeal R) n,
            g ≫ powerStageToSpec structureHom (maximalIdeal R) n = π i ≫ f :=
  Iff.rfl

/-- A morphism that factors through some maximal-ideal power stage fppf-locally factors through
a discrete valuation ring thickening. -/
theorem fppfLocallyFactorsThroughDvrStage.of_stage (R : Type u) [CommRing R]
    [IsLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) {T : Over S}
    (n : ℕ) (g : T ⟶ powerStage structureHom (maximalIdeal R) n) :
    fppfLocallyFactorsThroughDvrStage R structureHom
      (g ≫ powerStageToSpec structureHom (maximalIdeal R) n) :=
  sorry

/-- Fppf-local factoring through a discrete valuation ring thickening is stable
under precomposition in `Over S`. -/
theorem fppfLocallyFactorsThroughDvrStage_map (R : Type u) [CommRing R]
    [IsLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S)
    {T₁ T₂ : (Over S)ᵒᵖ} (h : T₁ ⟶ T₂) {f : T₁.unop ⟶ Over.mk structureHom}
    (hf : fppfLocallyFactorsThroughDvrStage R structureHom f) :
    fppfLocallyFactorsThroughDvrStage R structureHom (h.unop ≫ f) :=
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
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact Category.id_comp f.val
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact Category.assoc k.unop h.unop f.val

/-- Sections of `spf R structureHom` over `T` are morphisms `T ⟶ Spec(R)` over
`S` that fppf-locally factor through some infinitesimal neighbourhood. -/
theorem spf_obj (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S)
    (T : (Over S)ᵒᵖ) :
    (spf R structureHom).obj T =
      { f : T.unop ⟶ Over.mk structureHom //
        fppfLocallyFactorsThroughDvrStage R structureHom f } :=
  rfl

/-- The comparison from the `n`-th Yoneda thickening into the sheafy formal
spectrum. -/
def dvrStageι (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    yoneda.obj (powerStage structureHom (maximalIdeal R) n) ⟶ spf R structureHom where
  app T :=
    TypeCat.ofHom fun (g : T.unop ⟶ powerStage structureHom (maximalIdeal R) n) ↦
      ⟨g ≫ powerStageToSpec structureHom (maximalIdeal R) n,
        fppfLocallyFactorsThroughDvrStage.of_stage R structureHom n g⟩
  naturality := sorry

/-- The comparison `dvrStageι` composes a map into the `n`-th thickening with
the quotient-induced morphism to `Spec(R)`. -/
theorem dvrStageι_app (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (T : (Over S)ᵒᵖ)
    (g : T.unop ⟶ powerStage structureHom (maximalIdeal R) n) :
    ((dvrStageι R n structureHom).app T g).val = g ≫ powerStageToSpec structureHom (maximalIdeal R) n :=
  rfl

/-- The sheafification unit from the Yoneda colimit of thickenings to `spf`. -/
def spfPresheafToSpf (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    spfAdicCompletion structureHom (maximalIdeal R) ⟶ spf R structureHom :=
  colimit.desc (powerThickenings structureHom (maximalIdeal R) ⋙ yoneda)
    { pt := spf R structureHom
      ι := { app := fun n ↦ dvrStageι R n structureHom
             naturality := sorry } }

/-- The sheafification unit restricts to `dvrStageι` on each thickening. -/
theorem spfPresheafToSpf_fac (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] (n : ℕ) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) :
    colimit.ι (powerThickenings structureHom (maximalIdeal R) ⋙ yoneda) n ≫
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
    IsDirectedAffineThickeningColimit (powerThickenings structureHom (maximalIdeal R)) (spf R structureHom) :=
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

/-- The morphism `Spec(R') ⟶ Spec(R)` over `S` induced by an algebra map. -/
def specOverMap (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) ⟶
      Over.mk structureHom :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R R'))) rfl

/-- The underlying scheme morphism of `specOverMap` is `Spec.map` of the algebra
map. -/
theorem specOverMap_left (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) :
    (specOverMap R R' structureHom).left =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) :=
  rfl

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
  rfl

/-- The spectrum map of the identity algebra preserves each structure morphism. -/
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

/-- Spectrum maps of a tower of algebras compose compatibly with the base morphism. -/
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
