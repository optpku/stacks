module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.HomCongr
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat.Generators
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension

/-!
# Obstructions to infinitesimal module extensions

A prescribed ideal-action comparison determines an explicit degree-two Ext class by
composing a descended quotient extension with an injective-presentation extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite.IdealSheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]

/-- Pushforward comparison maps correspond bijectively to intrinsic ideal-action maps. -/
noncomputable def infinitesimalComparisonEquiv (F K : X.Modules) :
    (kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) ≃
      (idealModule i ⊗ F ⟶ K) :=
  ((pullbackPushforwardAdjunction i).homEquiv
    (kernelIdealSheaf i ⊗ (i _*).obj F) K).symm.trans
    (Iso.homCongr
      ((Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) ((i _*).obj F)).symm ≪≫
        tensorIso (Iso.refl (idealModule i))
          (@asIso _ _ _ _ ((pullbackPushforwardAdjunction i).counit.app F)
            (instIsIso_counit_app (i := i) (F := F))))
      (Iso.refl K))

/-- The comparison-map equivalence acts by restricting along the thickening. -/
theorem infinitesimalComparisonEquiv_apply (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    infinitesimalComparisonEquiv i F K c = infinitesimalMap_restrict i c := by
  simp only [infinitesimalComparisonEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Adjunction.homEquiv_counit, Iso.trans_inv, Iso.symm_inv, tensorIso_inv,
    Iso.refl_inv, Iso.refl_hom, Category.comp_id, Category.assoc,
    infinitesimalMap_restrict]
  rfl

-- Lean module compatibility: the exposed constructors must be able to use the
-- private sequence data and proof certificates without exporting their names.
set_option backward.privateInPublic true

namespace InfinitesimalExtension

/-- A chosen flat module covering the pushforward of a module. -/
private noncomputable def flatCover (F : X.Modules) : X'.Modules :=
  (exists_epi_from_flat ((i _*).obj F)).choose

/-- The chosen covering module is flat. -/
private instance flatCover_isFlat (F : X.Modules) : (flatCover i F).IsFlat :=
  (exists_epi_from_flat ((i _*).obj F)).choose_spec.choose

/-- The chosen covering epimorphism onto the pushforward module. -/
private noncomputable def flatCover_π (F : X.Modules) : flatCover i F ⟶ (i _*).obj F :=
  (exists_epi_from_flat ((i _*).obj F)).choose_spec.choose_spec.choose

/-- The chosen covering morphism is an epimorphism. -/
private instance flatCover_π_epi (F : X.Modules) : Epi (flatCover_π i F) :=
  (exists_epi_from_flat ((i _*).obj F)).choose_spec.choose_spec.choose_spec

/-- The kernel sequence of the chosen flat covering epimorphism. -/
private noncomputable def flatCoverKernelExtension (F : X.Modules) : ShortComplex X'.Modules :=
  ShortComplex.kernelSequence (flatCover_π i F)

/-- The kernel sequence of the covering epimorphism is short exact. -/
private theorem flatCoverKernelExtension_shortExact (F : X.Modules) :
    (flatCoverKernelExtension i F).ShortExact := sorry

/-- The ideal action lifted to the kernel annihilates the tensor of the kernel inclusion
after passage to the ideal quotient. -/
private theorem idealQuotientIncl_zero (F : X.Modules) :
    (tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F)) ≫
      (kernel.lift (flatCover_π i F) (action (kernelIdealSubobject i) (flatCover i F))
        (action_comp_π i (0 : (i _*).obj F ⟶ flatCover i F) (flatCover_π i F)) ≫
        cokernel.π (action (kernelIdealSubobject i) (kernel (flatCover_π i F)))) = 0 := sorry

/-- The comparison from the ideal quotient of the cover to the ideal quotient of its kernel. -/
private noncomputable def idealQuotientIncl (F : X.Modules) :
    cokernel ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F))) ⟶
      cokernel (action (kernelIdealSubobject i) (kernel (flatCover_π i F))) :=
  cokernel.desc
    ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F)))
    (kernel.lift (flatCover_π i F) (action (kernelIdealSubobject i) (flatCover i F))
        (action_comp_π i (0 : (i _*).obj F ⟶ flatCover i F) (flatCover_π i F)) ≫
      cokernel.π (action (kernelIdealSubobject i) (kernel (flatCover_π i F))))
    (idealQuotientIncl_zero i F)

/-- Pullback of the ideal-quotient comparison is a monomorphism. -/
private theorem idealQuotientIncl_pullback_mono (F : X.Modules) :
    Mono ((i ^*).map (idealQuotientIncl i F)) := sorry

/-- The tensor of the kernel inclusion is annihilated by the prescribed comparison. -/
private theorem idealQuotientToKernel_comp_zero (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F)) ≫
      ((tensorLeft (kernelIdealSheaf i)).map (flatCover_π i F) ≫ c) = 0 := sorry

/-- The map from the ideal quotient of the cover induced by a comparison map. -/
private noncomputable def idealQuotientToKernel (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    cokernel ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F))) ⟶
      (i _*).obj K :=
  cokernel.desc
    ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F)))
    ((tensorLeft (kernelIdealSheaf i)).map (flatCover_π i F) ≫ c)
    (idealQuotientToKernel_comp_zero i F K c)

/-- The quotient map recovers the prescribed comparison after tensoring the cover map. -/
private theorem idealQuotientToKernel_spec (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    cokernel.π ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F))) ≫
        idealQuotientToKernel i F K c =
      (tensorLeft (kernelIdealSheaf i)).map (flatCover_π i F) ≫ c := by
  exact cokernel.π_desc _ _ _

variable (F K : X.Modules)

/-- The kernel map obtained by extending the ideal-quotient map into an injective module. -/
private noncomputable def injectiveKernelMap [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    kernel (flatCover_π i F) ⟶ (i _*).obj K :=
  have := idealQuotientIncl_pullback_mono i F
  let g : _ ⟶ K := (i ^*).map (idealQuotientToKernel i F K c) ≫
    (pullbackPushforwardAdjunction i).counit.app K
  let γ := Injective.factorThru g ((i ^*).map (idealQuotientIncl i F))
  cokernel.π (action (kernelIdealSubobject i) (kernel (flatCover_π i F))) ≫
    (pullbackPushforwardAdjunction i).unit.app
      (cokernel (action (kernelIdealSubobject i) (kernel (flatCover_π i F)))) ≫
      (i _*).map γ

/-- The inclusion of the injective module in the pushout of the flat-cover kernel sequence. -/
private noncomputable def injectiveEnvelopeSequence_ι [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :=
  pushout.inl (injectiveKernelMap i F K c) (kernel.ι (flatCover_π i F))

/-- The projection from the injective pushout to the quotient module. -/
private noncomputable def injectiveEnvelopeSequence_π [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    pushout (injectiveKernelMap i F K c) (kernel.ι (flatCover_π i F)) ⟶ (i _*).obj F :=
  pushout.desc 0 (flatCover_π i F) (by simp)

/-- The two maps of the injective pushout sequence compose to zero. -/
private theorem injectiveEnvelopeSequence_zero [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    injectiveEnvelopeSequence_ι i F K c ≫ injectiveEnvelopeSequence_π i F K c = 0 := sorry

/-- The pushout sequence associated to an injective coefficient module. -/
private noncomputable def injectiveEnvelopeSequence [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) : ShortComplex X'.Modules :=
  ShortComplex.mk (injectiveEnvelopeSequence_ι i F K c)
    (injectiveEnvelopeSequence_π i F K c) (injectiveEnvelopeSequence_zero i F K c)

/-- The injective pushout sequence is short exact. -/
private theorem injectiveEnvelopeSequence_shortExact [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (injectiveEnvelopeSequence i F K c).ShortExact := by
  have hcover := flatCoverKernelExtension_shortExact i F
  sorry

/-- The ideal-action comparison of the injective pushout is the prescribed map. -/
private theorem injectiveEnvelopeSequence_infMap [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    infinitesimalMap i (injectiveEnvelopeSequence i F K c).f
      (injectiveEnvelopeSequence i F K c).g (injectiveEnvelopeSequence i F K c).zero
      (injectiveEnvelopeSequence_shortExact i F K c) = c := sorry

/-- An infinitesimal extension with injective coefficient module, constructed by pushing out
the kernel sequence of a flat cover along an injective lift. -/
noncomputable def ofInjective [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    InfinitesimalExtension i F K c :=
  of (injectiveEnvelopeSequence i F K c).X₂ (injectiveEnvelopeSequence i F K c).f
    (injectiveEnvelopeSequence i F K c).g (injectiveEnvelopeSequence i F K c).zero
    (injectiveEnvelopeSequence_shortExact i F K c) (injectiveEnvelopeSequence_infMap i F K c)

/-- The injective construction is short exact and has its prescribed infinitesimal map. -/
theorem ofInjective_spec [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (ShortComplex.mk (ofInjective i F K c).ι (ofInjective i F K c).π
        (ofInjective i F K c).w).ShortExact ∧
      infinitesimalMap i (ofInjective i F K c).ι (ofInjective i F K c).π
        (ofInjective i F K c).w (ofInjective i F K c).shortExact = c :=
  ⟨(ofInjective i F K c).shortExact, (ofInjective i F K c).infMap_eq⟩

/-- The cokernel sequence of the functorial injective embedding. -/
private noncomputable def injectiveCokernelExtension : ShortComplex X.Modules :=
  ShortComplex.cokernelSequence (HasFunctorialInjectives.ι.app K)

/-- The cokernel sequence of the injective embedding is short exact. -/
private theorem injectiveCokernelExtension_shortExact :
    (injectiveCokernelExtension K).ShortExact := sorry

/-- The infinitesimal extension obtained after embedding the coefficient in an injective. -/
private noncomputable def injectiveEnvelope
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :=
  ofInjective i F (HasFunctorialInjectives.obj K)
    (c ≫ (i _*).map (HasFunctorialInjectives.ι.app K))

/-- The inclusion of the coefficient quotient in the envelope pushout. -/
private noncomputable def envelopePushoutExtension_ι
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :=
  pushout.inl ((i _*).map (cokernel.π (HasFunctorialInjectives.ι.app K)))
    (injectiveEnvelope i F K c).ι

/-- The quotient projection out of the envelope pushout. -/
private noncomputable def envelopePushoutExtension_π
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    pushout ((i _*).map (cokernel.π (HasFunctorialInjectives.ι.app K)))
      (injectiveEnvelope i F K c).ι ⟶ (i _*).obj F :=
  pushout.desc 0 (injectiveEnvelope i F K c).π (by
    rw [comp_zero, (injectiveEnvelope i F K c).w])

/-- The envelope-pushout inclusion and projection compose to zero. -/
private theorem envelopePushoutExtension_zero
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    envelopePushoutExtension_ι i F K c ≫ envelopePushoutExtension_π i F K c = 0 := sorry

/-- The envelope pushed out along the injective-presentation quotient. -/
private noncomputable def envelopePushoutExtension
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) : ShortComplex X'.Modules :=
  ShortComplex.mk (envelopePushoutExtension_ι i F K c)
    (envelopePushoutExtension_π i F K c) (envelopePushoutExtension_zero i F K c)

/-- The envelope pushout sequence is short exact. -/
private theorem envelopePushoutExtension_shortExact
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (envelopePushoutExtension i F K c).ShortExact := sorry

/-- The ideal-action comparison of the envelope pushout vanishes. -/
private theorem envelopePushoutExtension_infMap_eq_zero
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    infinitesimalMap i (envelopePushoutExtension i F K c).f
      (envelopePushoutExtension i F K c).g (envelopePushoutExtension i F K c).zero
      (envelopePushoutExtension_shortExact i F K c) = 0 := sorry

/-- The counit-conjugated inclusion in the descended quotient sequence. -/
private noncomputable def quotientObstructionExtension_ι
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :=
  (asIso ((pullbackPushforwardAdjunction i).counit.app
    (cokernel (HasFunctorialInjectives.ι.app K)))).inv ≫
      (i ^*).map (envelopePushoutExtension i F K c).f

/-- The counit-conjugated projection in the descended quotient sequence. -/
private noncomputable def quotientObstructionExtension_π
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :=
  (i ^*).map (envelopePushoutExtension i F K c).g ≫
    (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom

/-- The descended quotient inclusion and projection compose to zero. -/
private theorem quotientObstructionExtension_zero
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    quotientObstructionExtension_ι i F K c ≫ quotientObstructionExtension_π i F K c = 0 := sorry

/-- The descended quotient sequence over the original ringed space. -/
private noncomputable def quotientObstructionExtension
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) : ShortComplex X.Modules :=
  ShortComplex.mk (quotientObstructionExtension_ι i F K c)
    (quotientObstructionExtension_π i F K c) (quotientObstructionExtension_zero i F K c)

/-- The descended quotient sequence is short exact, since the envelope pushout has zero
ideal-action comparison. -/
private theorem quotientObstructionExtension_shortExact
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (quotientObstructionExtension i F K c).ShortExact := by
  have hzero := envelopePushoutExtension_infMap_eq_zero i F K c
  have hpushout := envelopePushoutExtension_shortExact i F K c
  sorry

variable [HasExt.{u} X.Modules]

/-- The degree-two obstruction obtained by composing the descended quotient class with
the injective-presentation class. -/
noncomputable def existenceObstruction
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) : Ext F K 2 :=
  (quotientObstructionExtension_shortExact i F K c).extClass.comp
    (injectiveCokernelExtension_shortExact K).extClass (rfl : 1 + 1 = 2)

/-- The existence obstruction is the Yoneda composite of the quotient and presentation classes. -/
theorem existenceObstruction_eq
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    existenceObstruction i F K c =
      (quotientObstructionExtension_shortExact i F K c).extClass.comp
        (injectiveCokernelExtension_shortExact K).extClass (rfl : 1 + 1 = 2) := rfl

/-- Vanishing of the obstruction supplies a section of the descended quotient projection. -/
private theorem exists_section_of_eq_zero
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :
    ∃ s : F ⟶ (quotientObstructionExtension i F K c).X₂,
      s ≫ (quotientObstructionExtension i F K c).g = 𝟙 F := sorry

/-- A section of the descended quotient projection supplied by obstruction vanishing. -/
private noncomputable def vanishingSection
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :=
  (exists_section_of_eq_zero i F K c h).choose

/-- The envelope map to the quotient by the chosen section. -/
private noncomputable def vanishingMap
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :=
  pushout.inr ((i _*).map (cokernel.π (HasFunctorialInjectives.ι.app K)))
    (injectiveEnvelope i F K c).ι ≫
      (pullbackPushforwardAdjunction i).unit.app (envelopePushoutExtension i F K c).X₂ ≫
        (i _*).map (cokernel.π (vanishingSection i F K c h))

/-- The original coefficient inclusion is annihilated by the quotient-by-section map. -/
private theorem ofVanishing_lift_condition
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :
    ((i _*).map (HasFunctorialInjectives.ι.app K) ≫ (injectiveEnvelope i F K c).ι) ≫
      vanishingMap i F K c h = 0 := sorry

/-- The original coefficient inclusion lifted to the kernel of the quotient-by-section map. -/
private noncomputable def vanishingInclusion
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :=
  kernel.lift (vanishingMap i F K c h)
    ((i _*).map (HasFunctorialInjectives.ι.app K) ≫ (injectiveEnvelope i F K c).ι)
    (ofVanishing_lift_condition i F K c h)

/-- The quotient projection restricted to the kernel of the quotient-by-section map. -/
private noncomputable def vanishingProjection
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :=
  kernel.ι (vanishingMap i F K c h) ≫ (injectiveEnvelope i F K c).π

/-- The reconstructed kernel inclusion and quotient projection compose to zero. -/
private theorem ofVanishing_zero
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :
    vanishingInclusion i F K c h ≫ vanishingProjection i F K c h = 0 := sorry

/-- The sequence reconstructed as the kernel of the quotient-by-section map is short exact. -/
private theorem ofVanishing_shortExact
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :
    (ShortComplex.mk (vanishingInclusion i F K c h) (vanishingProjection i F K c h)
      (ofVanishing_zero i F K c h)).ShortExact := sorry

/-- The reconstructed kernel sequence has the prescribed ideal-action comparison. -/
private theorem ofVanishing_infMap
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :
    infinitesimalMap i (vanishingInclusion i F K c h) (vanishingProjection i F K c h)
      (ofVanishing_zero i F K c h) (ofVanishing_shortExact i F K c h) = c := sorry

/-- An infinitesimal extension reconstructed from obstruction vanishing as the kernel of
the envelope map to the quotient by a splitting of the descended sequence. -/
noncomputable def ofVanishing
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) : InfinitesimalExtension i F K c :=
  of (kernel (vanishingMap i F K c h)) (vanishingInclusion i F K c h)
    (vanishingProjection i F K c h) (ofVanishing_zero i F K c h)
    (ofVanishing_shortExact i F K c h) (ofVanishing_infMap i F K c h)

/-- The extension reconstructed from vanishing has the prescribed infinitesimal map. -/
theorem ofVanishing_spec
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :
    infinitesimalMap i (ofVanishing i F K c h).ι (ofVanishing i F K c h).π
      (ofVanishing i F K c h).w (ofVanishing i F K c h).shortExact = c :=
  (ofVanishing i F K c h).infMap_eq

/-- The existence obstruction vanishes for an injective coefficient module. -/
theorem existenceObstruction_eq_zero_of_injective [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    existenceObstruction i F K c = 0 := sorry

/-- The existence obstruction vanishes exactly when an infinitesimal extension with the
prescribed ideal-action comparison exists. -/
theorem existenceObstruction_eq_zero_iff
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    existenceObstruction i F K c = 0 ↔ Nonempty (InfinitesimalExtension i F K c) := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
