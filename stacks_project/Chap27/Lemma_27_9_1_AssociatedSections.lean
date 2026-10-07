module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk.Skyscraper
public import ReasLib.Algebra.Module.Graded.DegreeZero
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import stacks_project.Chap27.Lemma_27_8_7_AssociatedSheaf

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe uA uσ

namespace AlgebraicGeometry.Proj

variable {A : Type uA} {σ : Type uσ} [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {M : Type uA} [AddCommGroup M] [Module A M]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- The canonical ring map from the degree-zero part of the graded ring to global sections on
`Proj 𝒜`. -/
noncomputable def degreeZeroRingHom :
    𝒜 0 →+* (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op ⊤) :=
  (((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
    (AlgebraicGeometry.Proj.toSpecZero 𝒜).appTop).hom)

/-- The canonical degree-zero ring map agrees with the map induced by `Proj.toSpecZero`. -/
theorem degreeZeroRingHom_apply (a : 𝒜 0) :
    degreeZeroRingHom 𝒜 a =
      (((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
        (AlgebraicGeometry.Proj.toSpecZero 𝒜).appTop).hom) a := sorry

/-- Multiplication by a degree-zero ring element preserves the degree-zero module piece. -/
theorem smul_mem_degreeZeroPiece (a : 𝒜 0) (m : ℳ 0) :
    (a : A) • (m : M) ∈ ℳ 0 := sorry

/-- The canonical action of the degree-zero ring on the degree-zero piece of a graded module. -/
noncomputable instance (priority := 90) associatedDegreeZeroPieceModule :
    Module (𝒜 0) (ℳ 0) where
  smul a m := ⟨(a : A) • (m : M), smul_mem_degreeZeroPiece 𝒜 ℳ a m⟩
  one_smul := sorry
  mul_smul := sorry
  smul_add := sorry
  smul_zero := sorry
  add_smul := sorry
  zero_smul := sorry

/-- A degree-zero element, viewed as the fraction with denominator `1`, belongs to the
degree-zero localization at a point of `Proj 𝒜`. -/
theorem degreeZeroAtPoint_mem (m : ℳ 0) (x : AlgebraicGeometry.Proj 𝒜) :
    LocalizedModule.mk (m : M)
        (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) ∈
      degreeZeroLocalizedModule 𝒜 ℳ x.asHomogeneousIdeal.toIdeal.primeCompl := sorry

/-- The value at `x` of the global section determined by a degree-zero element. -/
noncomputable def degreeZeroAtPoint (m : ℳ 0) (x : AlgebraicGeometry.Proj 𝒜) :
    atPointModule 𝒜 ℳ x :=
  ⟨LocalizedModule.mk (m : M) (1 : x.asHomogeneousIdeal.toIdeal.primeCompl),
    degreeZeroAtPoint_mem 𝒜 ℳ m x⟩

/-- The point-family defined by a degree-zero element is locally representable. -/
theorem degreeZeroSection_isLocallyRepresentable (m : ℳ 0) :
    IsLocallyRepresentable 𝒜 ℳ ⊤ (fun x ↦ degreeZeroAtPoint 𝒜 ℳ m x.1) := sorry

/-- The global section of the associated sheaf defined by a degree-zero element. -/
noncomputable def degreeZeroSection (m : ℳ 0) : AssociatedSections 𝒜 ℳ ⊤ :=
  ⟨fun x ↦ degreeZeroAtPoint 𝒜 ℳ m x.1,
    degreeZeroSection_isLocallyRepresentable 𝒜 ℳ m⟩

/-- Evaluation of the global section associated to a degree-zero element is the fraction with
denominator `1`. -/
theorem degreeZeroSection_apply (m : ℳ 0) (x : AlgebraicGeometry.Proj 𝒜) :
    (degreeZeroSection 𝒜 ℳ m).1 ⟨x, trivial⟩ = degreeZeroAtPoint 𝒜 ℳ m x := sorry

/-- The canonical degree-zero homogeneous-piece map into global sections of the associated
sheaf, after restriction of scalars along `degreeZeroRingHom`. -/
noncomputable def degreeZeroSectionLinear :
    ℳ 0 →ₗ[𝒜 0]
      (ModuleCat.restrictScalars (degreeZeroRingHom 𝒜)).obj
        (associatedSectionModule 𝒜 ℳ ⊤) where
  toFun := degreeZeroSection 𝒜 ℳ
  map_add' := sorry
  map_smul' := sorry

/-- The degree-zero linear section map evaluates to `degreeZeroSection`. -/
theorem degreeZeroSectionLinear_apply (m : ℳ 0) :
    degreeZeroSectionLinear 𝒜 ℳ m = degreeZeroSection 𝒜 ℳ m := sorry

/-- The degree-zero section map bundled as a morphism after restriction of scalars. -/
noncomputable def degreeZeroSectionHom :
    ModuleCat.of (𝒜 0) (ℳ 0) ⟶
      (ModuleCat.restrictScalars (degreeZeroRingHom 𝒜)).obj
        (associatedSectionModule 𝒜 ℳ ⊤) :=
  let source := ModuleCat.of (𝒜 0) (ℳ 0)
  let target := (ModuleCat.restrictScalars (degreeZeroRingHom 𝒜)).obj
    (associatedSectionModule 𝒜 ℳ ⊤)
  @ModuleCat.ofHom (𝒜 0) _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    (degreeZeroSectionLinear 𝒜 ℳ)

/-- The bundled degree-zero section morphism evaluates to `degreeZeroSection`. -/
theorem degreeZeroSectionHom_apply (m : ℳ 0) :
    degreeZeroSectionHom 𝒜 ℳ m = degreeZeroSection 𝒜 ℳ m := sorry

/-- The standard-open section constructor as a linear map after scalar transport through
`Proj.basicOpenIsoAway`. -/
noncomputable def awaySectionLinear {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    awayModule 𝒜 ℳ f →ₗ[HomogeneousLocalization.Away 𝒜 (f : A)]
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
          (associatedSectionModule 𝒜 ℳ
            (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))) where
  toFun := awaySection 𝒜 ℳ f hd
  map_add' := sorry
  map_smul' := sorry

/-- The linear standard-open section map recovers the existing fraction section. -/
theorem awaySectionLinear_apply {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (z : awayModule 𝒜 ℳ f) :
    awaySectionLinear 𝒜 ℳ f hd z = awaySection 𝒜 ℳ f hd z := sorry

/-- The standard-open section map bundled as a morphism after scalar transport through
`Proj.basicOpenIsoAway`. -/
noncomputable def awaySectionHom {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    ModuleCat.of (HomogeneousLocalization.Away 𝒜 (f : A)) (awayModule 𝒜 ℳ f) ⟶
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
          (associatedSectionModule 𝒜 ℳ
            (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))) :=
  let source := ModuleCat.of (HomogeneousLocalization.Away 𝒜 (f : A)) (awayModule 𝒜 ℳ f)
  let target := (ModuleCat.restrictScalars
    (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
      (associatedSectionModule 𝒜 ℳ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)))
  @ModuleCat.ofHom (HomogeneousLocalization.Away 𝒜 (f : A)) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    (awaySectionLinear 𝒜 ℳ f hd)

/-- The bundled standard-open section morphism evaluates to `awaySection`. -/
theorem awaySectionHom_apply {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (z : awayModule 𝒜 ℳ f) :
    awaySectionHom 𝒜 ℳ f hd z = awaySection 𝒜 ℳ f hd z := sorry

/-- Evaluation of an associated section on an open neighborhood at a chosen point. -/
noncomputable def sectionEvaluation (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (x : AlgebraicGeometry.Proj 𝒜) (hx : x ∈ U) :
    associatedSectionModule 𝒜 ℳ U ⟶
      (ModuleCat.restrictScalars
        ((AlgebraicGeometry.Proj 𝒜).presheaf.germ U x hx).hom).obj
          (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
            (atPointModule 𝒜 ℳ x)) :=
  let source := associatedSectionModule 𝒜 ℳ U
  let target :=
    (ModuleCat.restrictScalars
      ((AlgebraicGeometry.Proj 𝒜).presheaf.germ U x hx).hom).obj
        (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
          (atPointModule 𝒜 ℳ x))
  @ModuleCat.ofHom ((AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun s ↦ s.1 ⟨x, hx⟩
      map_add' := sorry
      map_smul' := sorry }

/-- On an open containing `x`, section evaluation is literal evaluation of the point-family. -/
theorem sectionEvaluation_apply (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (x : AlgebraicGeometry.Proj 𝒜) (hx : x ∈ U) (s : AssociatedSections 𝒜 ℳ U) :
    sectionEvaluation 𝒜 ℳ U x hx s = s.1 ⟨x, hx⟩ := sorry

/-- The component of the associated-presheaf map to the skyscraper of the point localization. -/
noncomputable def stalkEvaluationSkyscraperApp (x : AlgebraicGeometry.Proj 𝒜)
    (U : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ) :
    (associatedPresheaf 𝒜 ℳ).obj U ⟶
      PresheafOfModules.Skyscraper.obj (AlgebraicGeometry.Proj 𝒜).presheaf x
        (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
          (atPointModule 𝒜 ℳ x)) U :=
  @dite _ (x ∈ U.unop) (Classical.dec _)
    (fun hx ↦ sectionEvaluation 𝒜 ℳ U.unop x hx ≫
      eqToHom (PresheafOfModules.Skyscraper.obj_eq_of_mem
        (AlgebraicGeometry.Proj 𝒜).presheaf x
        (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
          (atPointModule 𝒜 ℳ x)) U hx).symm)
    (fun _ ↦ 0)

/-- The skyscraper evaluation components commute with restriction. -/
theorem stalkEvaluationSkyscraperApp_naturality (x : AlgebraicGeometry.Proj 𝒜)
    {U V : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (i : U ⟶ V) :
    (associatedPresheaf 𝒜 ℳ).map i ≫
        (ModuleCat.restrictScalars
          ((AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj.map i).hom).map
            (stalkEvaluationSkyscraperApp 𝒜 ℳ x V) =
      stalkEvaluationSkyscraperApp 𝒜 ℳ x U ≫
        PresheafOfModules.Skyscraper.map (AlgebraicGeometry.Proj 𝒜).presheaf x
          (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
            (atPointModule 𝒜 ℳ x)) i := sorry

/-- The associated presheaf maps canonically to the skyscraper of its point localization. -/
noncomputable def stalkEvaluationSkyscraper (x : AlgebraicGeometry.Proj 𝒜) :
    associatedPresheaf 𝒜 ℳ ⟶
      PresheafOfModules.Skyscraper.atPoint (AlgebraicGeometry.Proj 𝒜).presheaf x
        (ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
          (atPointModule 𝒜 ℳ x)) where
  app := stalkEvaluationSkyscraperApp 𝒜 ℳ x
  naturality := stalkEvaluationSkyscraperApp_naturality 𝒜 ℳ x

/-- Evaluation of germs identifies the stalk of the associated sheaf with the degree-zero
localization at `x`. -/
noncomputable def stalkEvaluation (x : AlgebraicGeometry.Proj 𝒜) :
    RingedSpace.stalkModuleCat (associatedSheaf 𝒜 ℳ) x ⟶
      ModuleCat.of ((AlgebraicGeometry.Proj 𝒜).presheaf.stalk x)
        (atPointModule 𝒜 ℳ x) :=
  PresheafOfModules.Skyscraper.fromHom (AlgebraicGeometry.Proj 𝒜).presheaf x
    (stalkEvaluationSkyscraper 𝒜 ℳ x)

/-- Stalk evaluation sends the germ of a section to its value at the chosen point. -/
theorem stalkEvaluation_germ (x : AlgebraicGeometry.Proj 𝒜)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (hx : x ∈ U)
    (s : AssociatedSections 𝒜 ℳ U) :
    stalkEvaluation 𝒜 ℳ x
        (TopCat.Presheaf.germ (associatedSheaf 𝒜 ℳ).val.presheaf U x hx s) =
      s.1 ⟨x, hx⟩ := sorry

/-- Stalk evaluation for the associated sheaf is an isomorphism. -/
noncomputable instance stalkEvaluationIsIso (x : AlgebraicGeometry.Proj 𝒜) :
    IsIso (stalkEvaluation 𝒜 ℳ x) := sorry

end AlgebraicGeometry.Proj
