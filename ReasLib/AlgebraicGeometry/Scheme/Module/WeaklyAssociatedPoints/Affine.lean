module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly associated points on affine opens

Weak association for the sections of a quasicoherent scheme module over an
affine open agrees with weak association at the corresponding point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u v w z

/-- Torsion ideals commute with a localization map on a localized module. -/
private theorem torsionOf_localizedMap
    {R : Type u} {A : Type v} {M : Type w} {N : Type z}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (S : Submonoid R) [IsLocalization S A]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (m : M) :
    Ideal.torsionOf A N (f m) =
      (Ideal.torsionOf R M m).map (algebraMap R A) := by
  ext a
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective S a
  rw [Ideal.mem_torsionOf_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff]
  rw [← IsLocalizedModule.mk'_one S f m,
    IsLocalizedModule.mk'_smul_mk' A f,
    IsLocalizedModule.mk'_eq_zero']
  simp only [Ideal.mem_torsionOf_iff, Subtype.exists, exists_prop,
    Submonoid.smul_def, smul_smul]

/-- Weak association at a prime is equivalent to weak association at the maximal ideal after
localizing both the ring and the module at that prime. -/
private theorem isWeaklyAssociatedToModule_iff_maximalIdeal_of_isLocalizedModule
    {R : Type u} {A : Type v} {M : Type w} {N : Type z}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] [IsLocalRing A]
    (f : M →ₗ[R] N) [IsLocalizedModule p.primeCompl f] :
    Ideal.IsWeaklyAssociatedToModule R M p ↔
      Ideal.IsWeaklyAssociatedToModule A N (IsLocalRing.maximalIdeal A) := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨f m, ?_⟩
    rw [torsionOf_localizedMap p.primeCompl f m,
      IsLocalization.minimalPrimes_map p.primeCompl A]
    simpa only [Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A p] using hm
  · rintro ⟨n, hn⟩
    obtain ⟨⟨m, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective p.primeCompl f n
    refine ⟨m, ?_⟩
    have htorsion :
        Ideal.torsionOf A N (IsLocalizedModule.mk' f m s) =
          Ideal.torsionOf A N (f m) := by
      ext a
      simp only [Ideal.mem_torsionOf_iff]
      constructor
      · intro ha
        calc
          a • f m = a • (s.1 • IsLocalizedModule.mk' f m s) := by
            exact congrArg (a • ·) (IsLocalizedModule.mk'_cancel' f m s).symm
          _ = s.1 • (a • IsLocalizedModule.mk' f m s) := smul_comm _ _ _
          _ = 0 := by rw [ha, smul_zero]
      · intro ha
        apply (IsLocalizedModule.smul_injective f s)
        calc
          s.1 • (a • IsLocalizedModule.mk' f m s) =
              a • (s.1 • IsLocalizedModule.mk' f m s) := smul_comm _ _ _
          _ = a • f m :=
            congrArg (a • ·) (IsLocalizedModule.mk'_cancel' f m s)
          _ = 0 := ha
          _ = s.1 • 0 := (smul_zero _).symm
    change IsLocalRing.maximalIdeal A ∈
      (Ideal.torsionOf A N (IsLocalizedModule.mk' f m s)).minimalPrimes at hn
    rw [htorsion, torsionOf_localizedMap p.primeCompl f m,
      IsLocalization.minimalPrimes_map p.primeCompl A] at hn
    simpa only [Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A p] using hn

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a quasicoherent scheme module on an affine open, a prime of the section
ring is weakly associated to the module of sections exactly when the
corresponding point is weakly associated to the scheme module. -/
@[stacks 056M]
theorem mem_weaklyAssociatedPrimes_sections_iff_fromSpec_mem_weakAss
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U))) :
    p.asIdeal ∈ weaklyAssociatedPrimes (Γ(X, U)) (Γ(ℱ, U)) ↔
      hU.fromSpec p ∈ ℱ.weakAss := by
  let y : X := hU.fromSpec p
  have hy : y ∈ U := (hU.isoSpec.inv p).2
  -- Local instance justification (proof-local temporary data): use the canonical section-to-stalk algebra at `y`.
  letI : Algebra (Γ(X, U)) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
  -- Local instance justification (proof-local temporary data): use the affine localization description of the stalk at `y`.
  letI : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal :=
    hU.isLocalization_stalk' p hy
  let f : Γ(ℱ, U) →ₗ[Γ(X, U)]
      (ModuleCat.restrictScalars
        (algebraMap (Γ(X, U)) (X.presheaf.stalk y))).obj
          (RingedSpace.stalkModuleCat ℱ y) :=
    { toFun := fun m ↦ TopCat.Presheaf.germ ℱ.val.presheaf U y hy m
      map_add' := fun a b ↦ (TopCat.Presheaf.germ ℱ.val.presheaf U y hy).hom.map_add a b
      map_smul' := fun r m ↦ PresheafOfModules.germ_smul ℱ.val y U hy r m }
  have hf : IsLocalizedModule p.asIdeal.primeCompl f := by
    let G : (Spec (.of Γ(X, U))).Modules := ℱ.restrict hU.fromSpec
    let M₀ : ModuleCat Γ(X, U) := moduleSpecΓFunctor.obj G
    let f₀ : M₀ →ₗ[Γ(X, U)]
        (ModuleCat.of Γ(X, U) ((tilde M₀).presheaf.stalk p)) :=
      (tilde.toStalk M₀ p).hom
    let eIn : Γ(ℱ, U) ≃ₗ[Γ(X, U)] M₀ := by
      let htop : hU.fromSpec ''ᵁ (⊤ : (Spec (.of Γ(X, U))).Opens) = U :=
        hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
      -- Local instance justification (defeq pin): expose the transported section module on the image of the top open.
      letI imageModule : Module Γ(X, hU.fromSpec ''ᵁ (⊤ : (Spec (.of Γ(X, U))).Opens))
          Γ(ℱ, hU.fromSpec ''ᵁ (⊤ : (Spec (.of Γ(X, U))).Opens)) := inferInstance
      let eEq := ℱ.val.presheaf.mapIso (eqToIso htop).op
      let eIso := eEq ≪≫ (ℱ.restrictAppIso hU.fromSpec ⊤).symm
      let eAdd : Γ(ℱ, U) ≃+ M₀ :=
        { toFun := eIso.hom
          invFun := eIso.inv
          left_inv := eIso.hom_inv_id_apply
          right_inv := eIso.inv_hom_id_apply
          map_add' := fun a b ↦ eIso.hom.hom.map_add a b }
      refine { eAdd with map_smul' := ?_ }
      intro r m
      change (ℱ.restrictAppIso hU.fromSpec ⊤).inv
          (ℱ.val.map (eqToHom htop).op (r • m)) =
        r • (ℱ.restrictAppIso hU.fromSpec ⊤).inv
          (ℱ.val.map (eqToHom htop).op m)
      apply (ConcreteCategory.bijective_of_isIso
        (ℱ.restrictAppIso hU.fromSpec ⊤).hom).1
      change ℱ.val.presheaf.map (eqToHom htop).op (r • m) =
        imageModule.smul ((hU.fromSpec.appIso ⊤).inv
            ((Spec Γ(X, U)).presheaf.map (homOfLE le_rfl).op
              ((Scheme.ΓSpecIso Γ(X, U)).inv r)))
          (ℱ.val.presheaf.map (eqToHom htop).op m)
      have hmap :
          ℱ.val.presheaf.map (eqToHom htop).op (r • m) =
            imageModule.smul (X.presheaf.map (eqToHom htop).op r)
              (ℱ.val.presheaf.map (eqToHom htop).op m) := by
        exact ℱ.val.map_smul (eqToHom htop).op r m
      rw [hmap]
      congr 1
      apply (ConcreteCategory.bijective_of_isIso
        (hU.fromSpec.appIso ⊤).hom).1
      rw [Iso.inv_hom_id_apply]
      change (X.presheaf.map (eqToHom htop).op ≫
          (hU.fromSpec.appIso ⊤).hom) r =
        ((Scheme.ΓSpecIso Γ(X, U)).inv ≫
          (Spec Γ(X, U)).presheaf.map (homOfLE le_rfl).op) r
      simp only [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
      simp [Scheme.Hom.appLE, hU.fromSpec_app_self]
      convert rfl using 1
      rw [← (Spec Γ(X, U)).presheaf.map_comp_apply]
      simp only [Subsingleton.elim _
          (𝟙 (Opposite.op (⊤ : (Spec Γ(X, U)).Opens)))]
      exact (congrArg (fun k ↦ k ((Scheme.ΓSpecIso Γ(X, U)).inv r))
        ((Spec Γ(X, U)).presheaf.map_id
          (Opposite.op (⊤ : (Spec Γ(X, U)).Opens)))).symm
    let eOut :
        (ModuleCat.of Γ(X, U) ((tilde M₀).presheaf.stalk p)) ≃ₗ[Γ(X, U)]
          (ModuleCat.restrictScalars
            (algebraMap (Γ(X, U)) (X.presheaf.stalk y))).obj
              (RingedSpace.stalkModuleCat ℱ y) := by
      -- Local instance justification (proof-local temporary data): restriction preserves quasicoherence.
      haveI : G.IsQuasicoherent := inferInstance
      -- Local instance justification (proof-local temporary data): the affine tilde comparison is an isomorphism for a quasicoherent module.
      haveI hFrom : IsIso G.fromTildeΓ := inferInstance
      let A := (Spec Γ(X, U)).presheaf.stalk p
      let N₁ := RingedSpace.stalkModuleCat (tilde M₀) p
      let N₀ := RingedSpace.stalkModuleCat G p
      let N₂ := RingedSpace.stalkModuleCat ℱ y
      let hAN₀ : Module A N₀ := inferInstance
      let hXN₂ : Module (X.presheaf.stalk y) N₂ := inferInstance
      -- Local instance justification (defeq pin): use the composite global-section-to-stalk algebra map on the affine spectrum.
      letI : Algebra Γ(X, U) A :=
        ((Scheme.ΓSpecIso Γ(X, U)).inv ≫
          (Spec Γ(X, U)).presheaf.germ ⊤ p (by simp)).hom.toAlgebra
      -- Local instance justification (defeq pin): restrict the tilde stalk scalars along the affine stalk algebra map.
      letI : Module Γ(X, U) N₁ :=
        Module.compHom N₁ (algebraMap Γ(X, U) A)
      -- Local instance justification (defeq pin): restrict the module stalk scalars along the affine stalk algebra map.
      letI : Module Γ(X, U) N₀ :=
        Module.compHom N₀ (algebraMap Γ(X, U) A)
      -- Local instance justification (defeq pin): restrict the target stalk scalars along its section algebra map.
      letI : Module Γ(X, U) N₂ :=
        Module.compHom N₂ (algebraMap Γ(X, U) (X.presheaf.stalk y))
      -- Local instance justification (defeq pin): record the canonical scalar tower for the tilde stalk.
      letI : IsScalarTower Γ(X, U) A N₁ :=
        .of_algebraMap_smul fun _ _ ↦ rfl
      -- Local instance justification (defeq pin): record the canonical scalar tower for the restricted module stalk.
      letI : IsScalarTower Γ(X, U) A N₀ :=
        .of_algebraMap_smul fun _ _ ↦ rfl
      -- Local instance justification (defeq pin): record the canonical scalar tower for the target module stalk.
      letI : IsScalarTower Γ(X, U) (X.presheaf.stalk y) N₂ :=
        .of_algebraMap_smul fun _ _ ↦ rfl
      let eFrom : tilde M₀ ≅ G :=
        @asIso _ _ _ _ G.fromTildeΓ hFrom
      let e₁ := ((RingedSpace.stalkModuleFunctor p).mapIso eFrom).toLinearEquiv
        |>.restrictScalars Γ(X, U)
      let e₂ :
          (ModuleCat.of Γ(X, U) N₀) ≃ₗ[Γ(X, U)]
            (ModuleCat.restrictScalars
              (algebraMap (Γ(X, U)) (X.presheaf.stalk y))).obj
                (RingedSpace.stalkModuleCat ℱ y) := by
        let eIso := (Scheme.Modules.restrictStalkNatIso hU.fromSpec p).app ℱ
        let eAdd : N₀ ≃+ RingedSpace.stalkModuleCat ℱ y :=
          eIso.addCommGroupIsoToAddEquiv
        refine { eAdd with map_smul' := ?_ }
        intro r n
        obtain ⟨V, hpV, s, rfl⟩ := G.presheaf.exists_germ_eq n
        dsimp only [eAdd]
        let rV : Γ(Spec (.of Γ(X, U)), V) :=
          (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, U)).inv r)
        have hr : algebraMap Γ(X, U) A r =
            (Spec Γ(X, U)).presheaf.germ V p hpV rV := by
          change ((Scheme.ΓSpecIso Γ(X, U)).inv ≫
            (Spec Γ(X, U)).presheaf.germ ⊤ p (by simp)) r = _
          exact ((Spec Γ(X, U)).presheaf.germ_res_apply
            (homOfLE le_top) p hpV
              ((Scheme.ΓSpecIso Γ(X, U)).inv r)).symm
        have hleft : r • (show N₀ from G.presheaf.germ V p hpV s) =
            (show N₀ from G.presheaf.germ V p hpV (rV • s)) := by
          -- Local instance justification (defeq pin): restore the captured native stalk-module structure for this calculation.
          letI : Module ((Spec Γ(X, U)).presheaf.stalk p) N₀ := hAN₀
          change (algebraMap Γ(X, U)
              ((Spec Γ(X, U)).presheaf.stalk p) r) •
              (show N₀ from G.presheaf.germ V p hpV s) = _
          rw [hr]
          exact (PresheafOfModules.germ_smul G.val p V hpV rV s).symm
        rw [hleft]
        change eIso.hom (G.presheaf.germ V p hpV (rV • s)) = _
        have hnat := ConcreteCategory.congr_hom
          (Scheme.Modules.germ_restrictStalkNatIso_hom_app
            hU.fromSpec p ℱ hpV) (rV • s)
        have hnat' : eIso.hom (G.presheaf.germ V p hpV (rV • s)) =
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) y (by simpa [y]) (rV • s) := by
          change ((Scheme.Modules.restrictStalkNatIso hU.fromSpec p).hom.app ℱ)
              (((Scheme.Modules.restrictFunctor hU.fromSpec).obj ℱ).presheaf.germ
                V p hpV (rV • s)) =
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) (hU.fromSpec p) _ (rV • s)
          convert hnat using 1 <;> simp only [ConcreteCategory.comp_apply] <;> rfl
        rw [hnat']
        have hnat_s := ConcreteCategory.congr_hom
          (Scheme.Modules.germ_restrictStalkNatIso_hom_app
            hU.fromSpec p ℱ hpV) s
        have hnat_s' : eIso.hom (G.presheaf.germ V p hpV s) =
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) y (by simpa [y]) s := by
          change ((Scheme.Modules.restrictStalkNatIso hU.fromSpec p).hom.app ℱ)
              (((Scheme.Modules.restrictFunctor hU.fromSpec).obj ℱ).presheaf.germ
                V p hpV s) =
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) (hU.fromSpec p) _ s
          convert hnat_s using 1 <;> simp only [ConcreteCategory.comp_apply] <;> rfl
        have hsection :
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) y (by simpa [y])
                ((ℱ.restrictAppIso hU.fromSpec V).hom s) =
              eIso.hom (G.presheaf.germ V p hpV s) := by
          convert hnat_s'.symm using 1 <;> rfl
        have hscalar :
            X.presheaf.germ (hU.fromSpec ''ᵁ V) y (by simpa [y])
                ((hU.fromSpec.appIso V).inv rV) =
              algebraMap Γ(X, U) (X.presheaf.stalk y) r := by
          change X.presheaf.germ (hU.fromSpec ''ᵁ V) y _
              ((hU.fromSpec.appIso V).inv rV) =
            X.presheaf.germ U y hy r
          apply (ConcreteCategory.bijective_of_isIso
            (hU.fromSpec.stalkMap p)).1
          rw [Scheme.Hom.germ_stalkMap_apply,
            Scheme.Hom.germ_stalkMap_apply]
          change (((hU.fromSpec.appIso V).inv ≫
              hU.fromSpec.app (hU.fromSpec ''ᵁ V) ≫
              (Spec Γ(X, U)).presheaf.germ
                (hU.fromSpec ⁻¹ᵁ hU.fromSpec ''ᵁ V) p _) rV) =
            ((hU.fromSpec.app U ≫
              (Spec Γ(X, U)).presheaf.germ
                (hU.fromSpec ⁻¹ᵁ U) p _) r)
          rw [Scheme.Hom.appIso_inv_app_assoc,
            hU.fromSpec_app_self]
          simp only [Category.assoc]
          rw [TopCat.Presheaf.germ_res,
            TopCat.Presheaf.germ_res]
          exact hr.symm
        have hfinal :
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) y (by simpa [y]) (rV • s) =
              r • (show N₂ from eIso.hom (G.presheaf.germ V p hpV s)) := by
          -- Local instance justification (defeq pin): restore the captured native target-stalk module structure.
          letI : Module (X.presheaf.stalk y) N₂ := hXN₂
          change ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) y _
              ((ℱ.restrictAppIso hU.fromSpec V).hom (rV • s)) =
            (algebraMap Γ(X, U) (X.presheaf.stalk y) r) •
              (show N₂ from eIso.hom (G.presheaf.germ V p hpV s))
          rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
          refine (PresheafOfModules.germ_smul ℱ.val y
            (hU.fromSpec ''ᵁ V) _
            ((hU.fromSpec.appIso V).inv rV)
            ((ℱ.restrictAppIso hU.fromSpec V).hom s)).trans ?_
          exact (congrArg (fun a : X.presheaf.stalk y ↦
            a • (show N₂ from ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) y _
              ((ℱ.restrictAppIso hU.fromSpec V).hom s))) hscalar).trans
            (congrArg (fun m : N₂ ↦
              (algebraMap Γ(X, U) (X.presheaf.stalk y) r) • m) hsection)
        exact hfinal
      exact e₁.trans e₂
    let g := eOut.toLinearMap ∘ₗ f₀ ∘ₗ eIn.toLinearMap
    -- Local instance justification (proof-local temporary data): transport localization across the source linear equivalence.
    haveI : IsLocalizedModule p.asIdeal.primeCompl (f₀ ∘ₗ eIn.toLinearMap) :=
      IsLocalizedModule.of_linearEquiv_right p.asIdeal.primeCompl f₀ eIn
    -- Local instance justification (proof-local temporary data): transport localization across the target linear equivalence.
    haveI : IsLocalizedModule p.asIdeal.primeCompl g :=
      IsLocalizedModule.of_linearEquiv p.asIdeal.primeCompl
        (f₀ ∘ₗ eIn.toLinearMap) eOut
    have hgf : g = f := by
      apply LinearMap.ext
      intro m
      dsimp only [g, LinearMap.comp_apply]
      change ((Scheme.Modules.restrictStalkNatIso hU.fromSpec p).hom.app ℱ)
          ((RingedSpace.stalkModuleFunctor p).map G.fromTildeΓ
            (tilde.toStalk M₀ p (eIn m))) =
        ℱ.presheaf.germ U y hy m
      have hstalk :
          (RingedSpace.stalkModuleFunctor p).map G.fromTildeΓ
              (tilde.toStalk M₀ p (eIn m)) =
            G.presheaf.germ ⊤ p (by simp) (eIn m) := by
        calc
          _ = G.presheaf.germ ⊤ p (by simp)
                (((Scheme.Modules.toPresheaf (Spec (.of Γ(X, U)))).map
                    G.fromTildeΓ).app
                  (Opposite.op ⊤) (tilde.toOpen M₀ ⊤ (eIn m))) := by
              exact TopCat.Presheaf.stalkFunctor_map_germ_apply
                (F := (tilde M₀).presheaf) (G := G.presheaf)
                ⊤ p (by simp)
                  ((Scheme.Modules.toPresheaf (Spec (.of Γ(X, U)))).map
                    G.fromTildeΓ)
                  (tilde.toOpen M₀ ⊤ (eIn m))
          _ = _ := by
            change G.presheaf.germ ⊤ p _
                (G.fromTildeΓ.val.app
                  (Opposite.op ⊤) (tilde.toOpen M₀ ⊤ (eIn m))) = _
            have happ :
                G.fromTildeΓ.val.app (Opposite.op ⊤)
                    (tilde.toOpen M₀ ⊤ (eIn m)) =
                  G.val.map (homOfLE le_rfl).op (eIn m) := by
              change (modulesSpecToSheaf.map G.fromTildeΓ).hom.app
                    (Opposite.op ⊤)
                      (tilde.toOpen
                        ((modulesSpecToSheaf.obj G).presheaf.obj
                          (Opposite.op ⊤)) ⊤ (eIn m)) =
                (modulesSpecToSheaf.obj G).obj.map
                  (homOfLE le_rfl).op (eIn m)
              simpa only [ConcreteCategory.comp_apply] using
                ConcreteCategory.congr_hom
                  (Scheme.Modules.toOpen_fromTildeΓ_app G ⊤) (eIn m)
            rw [happ]
            exact G.presheaf.germ_res_apply
              (homOfLE le_rfl) p (by simp) (eIn m)
      rw [hstalk]
      have hnat := ConcreteCategory.congr_hom
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app
          hU.fromSpec p ℱ (by simp)) (eIn m)
      rw [show
        ((Scheme.Modules.restrictStalkNatIso hU.fromSpec p).hom.app ℱ)
            (G.presheaf.germ ⊤ p (by simp) (eIn m)) =
          ℱ.presheaf.germ (hU.fromSpec ''ᵁ (⊤ : (Spec (.of Γ(X, U))).Opens))
            y (by simpa [y]) (eIn m) by
        convert hnat using 1 <;> simp only [ConcreteCategory.comp_apply] <;> rfl]
      let htop : hU.fromSpec ''ᵁ
          (⊤ : (Spec (.of Γ(X, U))).Opens) = U :=
        hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
      dsimp only [eIn]
      change ℱ.presheaf.germ (hU.fromSpec ''ᵁ
          (⊤ : (Spec (.of Γ(X, U))).Opens)) y _
          (ℱ.val.presheaf.map (eqToHom htop).op m) =
        ℱ.presheaf.germ U y hy m
      exact ℱ.presheaf.germ_res_apply
        (eqToHom htop) y (by simpa [y]) m
    rw [← hgf]
    infer_instance
  -- Local instance justification (defeq pin): view the target stalk module over the affine section ring.
  letI : Module Γ(X, U) (RingedSpace.stalkModuleCat ℱ y) :=
    Module.compHom _ (algebraMap Γ(X, U) (X.presheaf.stalk y))
  -- Local instance justification (defeq pin): record the canonical scalar tower for the final localization comparison.
  letI : IsScalarTower Γ(X, U) (X.presheaf.stalk y)
      (RingedSpace.stalkModuleCat ℱ y) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  change Ideal.IsWeaklyAssociatedToModule (Γ(X, U)) (Γ(ℱ, U)) p.asIdeal ↔
    Ideal.IsWeaklyAssociatedToModule (X.presheaf.stalk y)
      (RingedSpace.stalkModuleCat ℱ y) (IsLocalRing.maximalIdeal _)
  exact isWeaklyAssociatedToModule_iff_maximalIdeal_of_isLocalizedModule
    p.asIdeal f

end AlgebraicGeometry.Scheme.Modules
