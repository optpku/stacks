module

public import ReasLib.AlgebraicGeometry.DividedPowers.Affine
public import stacks_project.Chap60.«60_8_1_2_CrystallineObject»
public import stacks_project.Chap60.Remark_60_5_4
public import ReasLib.RingTheory.DividedPowers.LocallyNilpotent
public import stacks_project.Chap60.«60_9_1_1_Site»
public import Mathlib.Algebra.Category.Grp.Abelian

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace CechCrisCover

/-- A ring map descends from a sufficiently deep source `p`-adic stage.
The inequality is essential when source and target towers have different offsets. -/
theorem adicStage_le_comap {B D : Type u} [CommRing B] [CommRing D]
    (p : ℕ) (f : B →+* D) {n m : ℕ} (hmn : m ≤ n) :
    Ideal.span ({(p : B)} : Set B) ^ n ≤
      (Ideal.span ({(p : D)} : Set D) ^ m).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span,
    Set.image_singleton, map_natCast]
  exact Ideal.pow_le_pow_right hmn

/-- Map between `p`-adic quotient rings at possibly different depths. -/
def adicStageMap {B D : Type u} [CommRing B] [CommRing D]
    (p : ℕ) (f : B →+* D) {n m : ℕ} (hmn : m ≤ n) :
    (B ⧸ Ideal.span ({(p : B)} : Set B) ^ n) →+*
      (D ⧸ Ideal.span ({(p : D)} : Set D) ^ m) :=
  Ideal.quotientMap _ f (adicStage_le_comap p f hmn)

/-- A nil divided-power ideal defines a genuine affine divided-power thickening. -/
theorem affineDividedPowerThickening {B : Type u} [CommRing B] {J : Ideal B}
    (δ : DividedPowers J) (hJ : ∀ x ∈ J, IsNilpotent x) :
    IsDividedPowerThickening (Spec (.of B)) (DividedPowers.affineIdeal (I := J))
      (DividedPowers.affine δ) (DividedPowers.affine_compatible δ) := sorry

/-- The geometric object of an affine PD thickening retains the whole ring
`B` as its thickening and `B/J` only as its closed fibre. The square is explicit
compatibility data for this low-level constructor. -/
noncomputable def affineCrystallineObject
    {S X : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        ((S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom))
    (x₀ : X ⟶ I.subscheme)
    {B : Type u} [CommRing B] (J : Ideal B) (δ : DividedPowers J)
    (hJ : ∀ x ∈ J, IsNilpotent x)
    (base : Spec (.of B) ⟶ S) (fibre : Spec (.of (B ⧸ J)) ⟶ X)
    (comm : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ base =
      fibre ≫ x₀ ≫ I.subschemeι) :
    CrystallineObject S I γ h_compatible X x₀ where
  source := Over.mk fibre
  thickening := Spec (.of B)
  thickeningToBase := base
  inclusion := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  ideal := DividedPowers.affineIdeal (I := J)
  gamma := DividedPowers.affine δ
  thickening_compatible := DividedPowers.affine_compatible δ
  isThickening := affineDividedPowerThickening δ hJ
  inclusion_isThickening := sorry
  ideal_eq_ker := sorry
  source_comm := comm

/-- Reindexed geometric stage maps induce a map on inverse-limit sections.
The index function may move to a deeper source stage for differing offsets. -/
noncomputable def sectionsMapOfStageMaps
    {D : Type v} [Category D] (F : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    [Limits.HasLimits AddCommGrpCat.{u}] (σ τ : ℕ ⥤ D)
    (k : ℕ →o ℕ) (t : ∀ e, τ.obj e ⟶ σ.obj (k e))
    (ht : ∀ (i j : ℕ) (h : i ≤ j),
      τ.map (homOfLE h) ≫ t j = t i ≫ σ.map (homOfLE (k.monotone h))) :
    Limits.limit (σ.op ⋙ F) ⟶ Limits.limit (τ.op ⋙ F) :=
  Limits.limit.lift (τ.op ⋙ F)
    { pt := Limits.limit (σ.op ⋙ F)
      π :=
        { app := fun e ↦ Limits.limit.π (σ.op ⋙ F) (Opposite.op (k e.unop)) ≫
            F.map (t e.unop).op
          naturality := sorry } }

section AffineStage

variable {p : ℕ} [Fact p.Prime]
variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable (hIC : Ideal.map (algebraMap A C) IA = ⊥) (hpnil : IsNilpotent (p : C))
variable {X : Scheme.{u}} (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ I.subscheme) (eX : Spec (.of C) ⟶ X)
variable (heX : eX ≫ x₀ ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))

include heX in
/-- The quotient square of an affine crystalline ring becomes the source/base
square of its geometric thickening. -/
theorem affineThickening_square
    (T : DividedPowerThickening.{u,u,u} p A IA γA C (algebraMap A C) hIC hpnil) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk T.B.ideal)) ≫
        Spec.map (CommRingCat.ofHom T.base.toRingHom) =
      (Spec.map (CommRingCat.ofHom T.quotient) ≫ eX) ≫ x₀ ≫ I.subschemeι := sorry

/-- Interpret an affine crystalline ring as a genuine geometric thickening.
This constructs an object of the large site; openness is checked separately
before using any such object in the small site. -/
noncomputable def affineThickeningObject
    (T : DividedPowerThickening.{u,u,u} p A IA γA C (algebraMap A C) hIC hpnil) :
    CrystallineObject (Spec (.of A)) I γS hc X x₀ :=
  affineCrystallineObject I γS hc x₀ T.B.ideal T.B.dividedPowers
    (fun _ hx ↦ mem_nilradical.mp
      ((T.B.dividedPowers.isLocallyNilpotent_of_isNilpotent_natCast T.p_nilpotent) hx))
    (Spec.map (CommRingCat.ofHom T.base.toRingHom))
    (Spec.map (CommRingCat.ofHom T.quotient) ≫ eX)
    (affineThickening_square γA hIC hpnil I x₀ eX heX T)

/-- A completed envelope is evaluated geometrically at its actual `p`-adic
quotient stage, with the entire quotient ring as thickening. -/
noncomputable def completedStageObject
    (Z : CompletedCrisObject p A IA γA C (algebraMap A C) hIC hpnil) (e : ℕ) :
    CrystallineObject (Spec (.of A)) I γS hc X x₀ :=
  affineThickeningObject γA hIC hpnil I γS hc x₀ eX heX
    (pAdicQuotientThickening γA (algebraMap A C) hIC hpnil Z e)

/-- A morphism of affine PD thickenings acts contravariantly on the whole
thickening spectra and on their closed fibres. Its PD hypothesis is retained. -/
noncomputable def affineThickeningMap
    {T U : DividedPowerThickening.{u,u,u} p A IA γA C (algebraMap A C) hIC hpnil}
    (f : DividedPowerThickening.Hom γA (algebraMap A C) T U) :
    CrystallineObject.Hom
      (affineThickeningObject γA hIC hpnil I γS hc x₀ eX heX U)
      (affineThickeningObject γA hIC hpnil I γS hc x₀ eX heX T) where
  source := Over.homMk (Spec.map (CommRingCat.ofHom (DividedPowerRing.quotientMap f.map)))
    sorry
  thickening := Spec.map (CommRingCat.ofHom f.map.toRingHom)
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- The thickening retained at a completed stage is the whole `p`-adic quotient
ring, rather than the quotient by its PD ideal. -/
theorem completedStageObject_thickening
    (Z : CompletedCrisObject p A IA γA C (algebraMap A C) hIC hpnil) (e : ℕ) :
    (completedStageObject γA hIC hpnil I γS hc x₀ eX heX Z e).thickening =
      Spec (.of (pAdicQuotientRing γA (algebraMap A C) hIC hpnil Z e)) := rfl

/-- Affine extension of the base divided powers agrees on every affine open
with the given compatible structure, provided it agrees globally. -/
theorem completedStageObject_baseCompatible
    (hI : I = DividedPowers.affineIdeal (I := IA))
    (hγ : DividedPowers.IsDPMorphism γA
      (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)
    (Z : CompletedCrisObject p A IA γA C (algebraMap A C) hIC hpnil) (e : ℕ) :
    CrystallineBaseCompatible I γS hc x₀
      (completedStageObject γA hIC hpnil I γS hc x₀ eX heX Z e) := sorry

/-- The closed fibre of a completed stage is `Spec C`. Thus an open chart
remains an open source after passing to the stage's geometric object. -/
theorem completedStageObject_open (ho : IsOpenImmersion eX)
    (Z : CompletedCrisObject p A IA γA C (algebraMap A C) hIC hpnil) (e : ℕ) :
    IsOpenImmersion
      (completedStageObject γA hIC hpnil I γS hc x₀ eX heX Z e).source.hom := sorry

/-- A genuine completed-envelope stage in the small crystalline site. Unlike
an arbitrary affine crystalline ring, it has closed fibre equal to the chart. -/
noncomputable def completedSmallStage
    (hI : I = DividedPowers.affineIdeal (I := IA))
    (hγ : DividedPowers.IsDPMorphism γA
      (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)
    (ho : IsOpenImmersion eX)
    (Z : CompletedCrisObject p A IA γA C (algebraMap A C) hIC hpnil) (e : ℕ) :
    Scheme.Crystalline.smallCrystallineSite (Spec (.of A)) I γS hc X x₀ where
  obj := ⟨completedStageObject γA hIC hpnil I γS hc x₀ eX heX Z e,
    completedStageObject_baseCompatible γA hIC hpnil I γS hc x₀ eX heX hI hγ Z e⟩
  property := completedStageObject_open γA hIC hpnil I γS hc x₀ eX heX ho Z e

variable (hI : I = DividedPowers.affineIdeal (I := IA))
variable (hγ : DividedPowers.IsDPMorphism γA
  (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)
variable (ho : IsOpenImmersion eX)
variable (Z : CompletedCrisObject p A IA γA C (algebraMap A C) hIC hpnil)

/-- The actual closed immersion between consecutive completed-envelope stages. -/
noncomputable def completedSmallStep (e : ℕ) :
    completedSmallStage γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z e ⟶
      completedSmallStage γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z (e + 1) :=
  ObjectProperty.homMk
    (affineThickeningMap γA hIC hpnil I γS hc x₀ eX heX
      (pAdicQuotientStep γA (algebraMap A C) hIC hpnil Z e).hom)

/-- The direct system of geometric thickenings corresponding to the inverse
system of quotient rings. -/
noncomputable def completedSmallSystem :
    ℕ ⥤ Scheme.Crystalline.smallCrystallineSite (Spec (.of A)) I γS hc X x₀ :=
  Functor.ofSequence (completedSmallStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z)

/-- Evaluate a presheaf on the genuine geometric stages, then take its inverse
limit. No stage is replaced by its trivial closed-fibre thickening. -/
noncomputable def completedSections
    (F : (Scheme.Crystalline.smallCrystallineSite (Spec (.of A)) I γS hc X x₀)ᵒᵖ ⥤
      AddCommGrpCat.{u}) [Limits.HasLimits AddCommGrpCat.{u}] : AddCommGrpCat.{u} :=
  Limits.limit
    ((completedSmallSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z).op ⋙ F)

variable {C' : Type u} [CommRing C'] [Algebra A C']
variable (hIC' : Ideal.map (algebraMap A C') IA = ⊥) (hpnil' : IsNilpotent (p : C'))
variable (W : CompletedCrisObject p A IA γA C' (algebraMap A C') hIC' hpnil')
variable (φ : DividedPowers.DPMorphism Z.B.dividedPowers W.B.dividedPowers)

/-- A sufficiently deep source index for mapping into target stage `e`. -/
noncomputable def crossStageIndex : ℕ →o ℕ where
  toFun e := e + pAdicOffset γA (algebraMap A C') hIC' hpnil' W
  monotone' := fun _ _ h ↦ Nat.add_le_add_right h _

/-- Completed PD-ring maps descend after shifting by the target offset. -/
noncomputable def crossStageRingHom (e : ℕ) :
    pAdicQuotientRing γA (algebraMap A C) hIC hpnil Z
        (crossStageIndex γA hIC' hpnil' W e) →+*
      pAdicQuotientRing γA (algebraMap A C') hIC' hpnil' W e :=
  adicStageMap p φ.toRingHom
    (Nat.le_add_right (e + pAdicOffset γA (algebraMap A C') hIC' hpnil' W)
      (pAdicOffset γA (algebraMap A C) hIC hpnil Z))

/-- The shifted quotient map preserves the induced divided powers because
the input map is a PD morphism and both quotients are PD-stable. -/
theorem crossStageRingHom_isDPMorphism (e : ℕ) :
    DividedPowers.IsDPMorphism
      (pAdicQuotientRing γA (algebraMap A C) hIC hpnil Z
        (crossStageIndex γA hIC' hpnil' W e)).dividedPowers
      (pAdicQuotientRing γA (algebraMap A C') hIC' hpnil' W e).dividedPowers
      (crossStageRingHom γA hIC hpnil Z hIC' hpnil' W φ e) := sorry

/-- The shifted comparison bundled as a genuine PD morphism. -/
noncomputable def crossStageDPHom (e : ℕ) :
    DividedPowers.DPMorphism
      (pAdicQuotientRing γA (algebraMap A C) hIC hpnil Z
        (crossStageIndex γA hIC' hpnil' W e)).dividedPowers
      (pAdicQuotientRing γA (algebraMap A C') hIC' hpnil' W e).dividedPowers :=
  DividedPowers.DPMorphism.mk'
    (crossStageRingHom_isDPMorphism γA hIC hpnil Z hIC' hpnil' W φ e)

variable (eX' : Spec (.of C') ⟶ X)
variable (heX' : eX' ≫ x₀ ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C')))
variable (ho' : IsOpenImmersion eX')

/-- A comparison between completed envelopes over two open charts induces a
geometric map after shifting the source stage. Base and closed-fibre squares
are required explicitly; an arbitrary ring map cannot supply this morphism. -/
noncomputable def crossSmallStageMap
    (g : C →+* C')
    (hbase : φ.toRingHom.comp Z.base.toRingHom = W.base.toRingHom)
    (hquot : W.toC.comp φ.toRingHom = g.comp Z.toC)
    (hchart : Spec.map (CommRingCat.ofHom g) ≫ eX = eX') (e : ℕ) :
    completedSmallStage γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W e ⟶
      completedSmallStage γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z
        (crossStageIndex γA hIC' hpnil' W e) :=
  ObjectProperty.homMk
    { source := Over.homMk
        (Spec.map (CommRingCat.ofHom (DividedPowerRing.quotientMap
          (crossStageDPHom γA hIC hpnil Z hIC' hpnil' W φ e)))) sorry
      thickening := Spec.map
        (CommRingCat.ofHom (crossStageRingHom γA hIC hpnil Z hIC' hpnil' W φ e))
      source_comm := sorry
      base_comm := sorry
      ideal_compatible := sorry
      dividedPowers_compatible := sorry }

variable (g : C →+* C')
variable (hbase : φ.toRingHom.comp Z.base.toRingHom = W.base.toRingHom)
variable (hquot : W.toC.comp φ.toRingHom = g.comp Z.toC)
variable (hchart : Spec.map (CommRingCat.ofHom g) ≫ eX = eX')

/-- The shifted cross-chart maps commute with all geometric stage transitions. -/
theorem crossSmallStageMap_naturality (i j : ℕ) (h : i ≤ j) :
    (completedSmallSystem γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W).map
        (homOfLE h) ≫
      crossSmallStageMap γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z
        hIC' hpnil' W φ eX' heX' ho' g hbase hquot hchart j =
    crossSmallStageMap γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z
        hIC' hpnil' W φ eX' heX' ho' g hbase hquot hchart i ≫
      (completedSmallSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z).map
        (homOfLE ((crossStageIndex γA hIC' hpnil' W).monotone h)) := sorry

/-- The cross-chart comparison of inverse-limit sections induced by a
compatible morphism of completed PD envelopes. -/
noncomputable def crossCompletedSectionsMap
    (F : (Scheme.Crystalline.smallCrystallineSite (Spec (.of A)) I γS hc X x₀)ᵒᵖ ⥤
      AddCommGrpCat.{u}) [Limits.HasLimits AddCommGrpCat.{u}] :
    completedSections γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F ⟶
      completedSections γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W F :=
  sectionsMapOfStageMaps F
    (completedSmallSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z)
    (completedSmallSystem γA hIC' hpnil' I γS hc x₀ eX' heX' hI hγ ho' W)
    (crossStageIndex γA hIC' hpnil' W)
    (crossSmallStageMap γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z
      hIC' hpnil' W φ eX' heX' ho' g hbase hquot hchart)
    (crossSmallStageMap_naturality γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z
      hIC' hpnil' W φ eX' heX' ho' g hbase hquot hchart)

end AffineStage

/-- Each component of the reindexed limit map is the specified stage map,
so the construction cannot silently replace that map by an arbitrary one. -/
theorem sectionsMapOfStageMaps_π
    {D : Type v} [Category D] (F : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    [Limits.HasLimits AddCommGrpCat.{u}] (σ τ : ℕ ⥤ D)
    (k : ℕ →o ℕ) (t : ∀ e, τ.obj e ⟶ σ.obj (k e))
    (ht : ∀ (i j : ℕ) (h : i ≤ j),
      τ.map (homOfLE h) ≫ t j = t i ≫ σ.map (homOfLE (k.monotone h))) (e : ℕ) :
    sectionsMapOfStageMaps F σ τ k t ht ≫ Limits.limit.π (τ.op ⋙ F) (Opposite.op e) =
      Limits.limit.π (σ.op ⋙ F) (Opposite.op (k e)) ≫ F.map (t e).op := by
  simp only [sectionsMapOfStageMaps, Limits.limit.lift_π]
  rfl

end CechCrisCover
