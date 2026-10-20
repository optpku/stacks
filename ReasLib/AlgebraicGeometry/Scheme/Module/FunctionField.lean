module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Module stalks in the function field

This file bundles the canonical specialization map from a module stalk to the stalk at the
generic point and records its functoriality and localization property.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

/-- The canonical specialization map from a module stalk to the generic stalk respects scalar
multiplication through the canonical map to the function field. -/
theorem stalkToFunctionField_map_smul (ℱ : X.Modules) (x : X)
    (r : X.presheaf.stalk x)
    (m : RingedSpace.stalkModuleCat
      (X := X.toLocallyRingedSpace.toRingedSpace) ℱ x) :
    TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf
        ((genericPoint_spec X).specializes trivial) (r • m) =
      algebraMap (X.presheaf.stalk x) X.functionField r •
        TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf
          ((genericPoint_spec X).specializes trivial) m := by
  let h := (genericPoint_spec X).specializes (show x ∈ Set.univ from trivial)
  obtain ⟨U, hxU, a, ha⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨V, hxV, b, hb⟩ := TopCat.Presheaf.exists_germ_eq ℱ.val.presheaf m
  let W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hηW : genericPoint X ∈ W := h.mem_open W.isOpen hxW
  let aW : X.presheaf.obj (op W) :=
    X.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op a
  let bW : ℱ.val.obj (op W) :=
    ℱ.val.presheaf.map (homOfLE (show W ≤ V from inf_le_right)).op b
  have haW : X.presheaf.germ W x hxW aW = r :=
    (X.presheaf.germ_res_apply (homOfLE (show W ≤ U from inf_le_left)) x hxW a).trans ha
  have hbW : TopCat.Presheaf.germ ℱ.val.presheaf W x hxW bW = m :=
    (TopCat.Presheaf.germ_res_apply ℱ.val.presheaf
      (homOfLE (show W ≤ V from inf_le_right)) x hxW b).trans hb
  calc
    TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf h (r • m) =
        TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf h
          (TopCat.Presheaf.germ ℱ.val.presheaf W x hxW (aW • bW)) := by
      congr 1
      exact (congrArg₂ (· • ·) haW hbW).symm.trans
        (PresheafOfModules.germ_smul ℱ.val x W hxW aW bW).symm
    _ = TopCat.Presheaf.germ ℱ.val.presheaf W (genericPoint X) hηW (aW • bW) := by
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    _ = X.presheaf.germ W (genericPoint X) hηW aW •
        TopCat.Presheaf.germ ℱ.val.presheaf W (genericPoint X) hηW bW :=
      PresheafOfModules.germ_smul ℱ.val (genericPoint X) W hηW aW bW
    _ = algebraMap (X.presheaf.stalk x) X.functionField r •
        TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf h m := by
      change _ = X.presheaf.stalkSpecializes h r •
        TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf h m
      rw [← haW, ← hbW, TopCat.Presheaf.germ_stalkSpecializes_apply,
        TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- The canonical module morphism from the stalk at a point to the generic stalk, regarded by
restriction of scalars as a module over the local ring at that point. -/
noncomputable def stalkToFunctionField (ℱ : X.Modules) (x : X) :
    RingedSpace.stalkModuleCat (X := X.toLocallyRingedSpace.toRingedSpace) ℱ x ⟶
      (ModuleCat.restrictScalars
        (algebraMap (X.presheaf.stalk x) X.functionField)).obj
          (RingedSpace.stalkModuleCat
            (X := X.toLocallyRingedSpace.toRingedSpace) ℱ (genericPoint X)) :=
  (ModuleCat.semilinearMapAddEquiv (algebraMap (X.presheaf.stalk x) X.functionField)
    (RingedSpace.stalkModuleCat (X := X.toLocallyRingedSpace.toRingedSpace) ℱ x)
    (RingedSpace.stalkModuleCat
      (X := X.toLocallyRingedSpace.toRingedSpace) ℱ (genericPoint X)))
    { toFun := fun m : TopCat.Presheaf.stalk
        (C := AddCommGrpCat.{u}) ℱ.val.presheaf x ↦
        TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf
          ((genericPoint_spec X).specializes
            (show x ∈ Set.univ from trivial)) m
      map_add' := fun m n ↦
        (TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf
          ((genericPoint_spec X).specializes
            (show x ∈ Set.univ from trivial))).hom.map_add m n
      map_smul' := stalkToFunctionField_map_smul ℱ x }

/-- The underlying function of `stalkToFunctionField` is the canonical specialization map on
additive stalks. -/
theorem stalkToFunctionField_apply (ℱ : X.Modules) (x : X)
    (m : RingedSpace.stalkModuleCat
      (X := X.toLocallyRingedSpace.toRingedSpace) ℱ x) :
    stalkToFunctionField ℱ x m =
      TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf
        ((genericPoint_spec X).specializes trivial) m := rfl

/-- The canonical maps from module stalks to the function field commute with morphisms of module
sheaves. -/
theorem stalkToFunctionField_naturality {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (x : X) :
    stalkToFunctionField ℱ x ≫
        (ModuleCat.restrictScalars
          (algebraMap (X.presheaf.stalk x) X.functionField)).map
            (RingedSpace.moduleStalkHom
              (X := X.toLocallyRingedSpace.toRingedSpace) (genericPoint X) φ) =
      RingedSpace.moduleStalkHom
        (X := X.toLocallyRingedSpace.toRingedSpace) x φ ≫ stalkToFunctionField 𝒢 x := by
  ext m
  exact TopCat.Presheaf.stalkSpecializes_stalkFunctor_map_apply
    ((PresheafOfModules.toPresheaf _).map φ.val)
      ((genericPoint_spec X).specializes trivial) m

set_option maxHeartbeats 800000 in
/-- For a quasicoherent module sheaf, the canonical map from a stalk to the generic stalk
exhibits the latter as localization at the non-zero-divisors of the local ring. -/
theorem isLocalizedModule_stalkToFunctionField (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x : X) :
    IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x))
      (stalkToFunctionField ℱ x).hom := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have sectionToStalk_isLocalized (p : PrimeSpectrum Γ(X, U))
      (hp : hU.fromSpec p ∈ U) :
      IsLocalizedModule p.asIdeal.primeCompl
        ({ toFun := fun m ↦ ℱ.presheaf.germ U (hU.fromSpec p) hp m
           map_add' := fun a b ↦
             (TopCat.Presheaf.germ ℱ.val.presheaf U (hU.fromSpec p) hp).hom.map_add a b
           map_smul' := fun r m ↦ PresheafOfModules.germ_smul ℱ.val
             (hU.fromSpec p) U hp r m } :
          Γ(ℱ, U) →ₗ[Γ(X, U)]
            (ModuleCat.restrictScalars
              (X.presheaf.germ U (hU.fromSpec p) hp).hom).obj
                (RingedSpace.stalkModuleCat ℱ (hU.fromSpec p))) := by
    -- Local instance justification (proof-local temporary data): expose the section-to-stalk
    -- algebra map while comparing the affine tilde model with the given module sheaf.
    letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) :=
      (X.presheaf.germ U (hU.fromSpec p) hp).hom.toAlgebra
    let G : (Spec (.of Γ(X, U))).Modules := ℱ.restrict hU.fromSpec
    let M₀ : ModuleCat Γ(X, U) := moduleSpecΓFunctor.obj G
    let f₀ : M₀ →ₗ[Γ(X, U)]
        (ModuleCat.of Γ(X, U) ((tilde M₀).presheaf.stalk p)) :=
      (tilde.toStalk M₀ p).hom
    let eIn : Γ(ℱ, U) ≃ₗ[Γ(X, U)] M₀ := by
      let htop : hU.fromSpec ''ᵁ (⊤ : (Spec (.of Γ(X, U))).Opens) = U :=
        hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
      -- Local instance justification (defeq pin): expose the transported section module on the
      -- image of the top open while constructing the canonical restriction equivalence.
      letI imageModule : Module Γ(X, hU.fromSpec ''ᵁ
          (⊤ : (Spec (.of Γ(X, U))).Opens))
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
            (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)))).obj
              (RingedSpace.stalkModuleCat ℱ (hU.fromSpec p)) := by
      -- Local instance justification (proof-local temporary data): restriction preserves the
      -- given quasicoherence while constructing the stalk comparison.
      haveI : G.IsQuasicoherent := inferInstance
      -- Local instance justification (proof-local temporary data): the affine tilde comparison
      -- is invertible for the restricted quasicoherent module.
      haveI hFrom : IsIso G.fromTildeΓ := inferInstance
      let A := (Spec Γ(X, U)).presheaf.stalk p
      let N₁ := RingedSpace.stalkModuleCat (tilde M₀) p
      let N₀ := RingedSpace.stalkModuleCat G p
      let N₂ := RingedSpace.stalkModuleCat ℱ (hU.fromSpec p)
      let hAN₀ : Module A N₀ := inferInstance
      let hXN₂ : Module (X.presheaf.stalk (hU.fromSpec p)) N₂ := inferInstance
      -- Local instance justification (defeq pin): expose the canonical section-to-stalk algebra
      -- map on the affine spectrum.
      letI : Algebra Γ(X, U) A :=
        ((Scheme.ΓSpecIso Γ(X, U)).inv ≫
          (Spec Γ(X, U)).presheaf.germ ⊤ p (by simp)).hom.toAlgebra
      -- Local instance justification (defeq pin): restrict the tilde stalk scalars along the
      -- affine stalk algebra map.
      letI : Module Γ(X, U) N₁ := Module.compHom N₁ (algebraMap Γ(X, U) A)
      -- Local instance justification (defeq pin): restrict the module stalk scalars along the
      -- affine stalk algebra map.
      letI : Module Γ(X, U) N₀ := Module.compHom N₀ (algebraMap Γ(X, U) A)
      -- Local instance justification (defeq pin): restrict the target stalk scalars along its
      -- section algebra map.
      letI : Module Γ(X, U) N₂ :=
        Module.compHom N₂ (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)))
      -- Local instance justification (defeq pin): record the canonical scalar tower for the
      -- tilde stalk.
      letI : IsScalarTower Γ(X, U) A N₁ := .of_algebraMap_smul fun _ _ ↦ rfl
      -- Local instance justification (defeq pin): record the canonical scalar tower for the
      -- restricted module stalk.
      letI : IsScalarTower Γ(X, U) A N₀ := .of_algebraMap_smul fun _ _ ↦ rfl
      -- Local instance justification (defeq pin): record the canonical scalar tower for the
      -- target stalk.
      letI : IsScalarTower Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) N₂ :=
        .of_algebraMap_smul fun _ _ ↦ rfl
      let eFrom : tilde M₀ ≅ G := @asIso _ _ _ _ G.fromTildeΓ hFrom
      let e₁ := ((RingedSpace.stalkModuleFunctor p).mapIso eFrom).toLinearEquiv
        |>.restrictScalars Γ(X, U)
      let e₂ :
          (ModuleCat.of Γ(X, U) N₀) ≃ₗ[Γ(X, U)]
            (ModuleCat.restrictScalars
              (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)))).obj
                (RingedSpace.stalkModuleCat ℱ (hU.fromSpec p)) := by
        let eIso := (Scheme.Modules.restrictStalkNatIso hU.fromSpec p).app ℱ
        let eAdd : N₀ ≃+ RingedSpace.stalkModuleCat ℱ (hU.fromSpec p) :=
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
            (homOfLE le_top) p hpV ((Scheme.ΓSpecIso Γ(X, U)).inv r)).symm
        have hleft : r • (show N₀ from G.presheaf.germ V p hpV s) =
            (show N₀ from G.presheaf.germ V p hpV (rV • s)) := by
          -- Local instance justification (defeq pin): restore the native stalk-module structure
          -- for this scalar computation.
          letI : Module ((Spec Γ(X, U)).presheaf.stalk p) N₀ := hAN₀
          change (algebraMap Γ(X, U) ((Spec Γ(X, U)).presheaf.stalk p) r) •
              (show N₀ from G.presheaf.germ V p hpV s) = _
          rw [hr]
          exact (PresheafOfModules.germ_smul G.val p V hpV rV s).symm
        rw [hleft]
        change eIso.hom (G.presheaf.germ V p hpV (rV • s)) = _
        have hnat := ConcreteCategory.congr_hom
          (Scheme.Modules.germ_restrictStalkNatIso_hom_app hU.fromSpec p ℱ hpV) (rV • s)
        have hnat' : eIso.hom (G.presheaf.germ V p hpV (rV • s)) =
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) (hU.fromSpec p) (by simpa) (rV • s) := by
          convert hnat using 1 <;> simp only [ConcreteCategory.comp_apply] <;> rfl
        rw [hnat']
        have hnat_s := ConcreteCategory.congr_hom
          (Scheme.Modules.germ_restrictStalkNatIso_hom_app hU.fromSpec p ℱ hpV) s
        have hnat_s' : eIso.hom (G.presheaf.germ V p hpV s) =
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) (hU.fromSpec p) (by simpa) s := by
          convert hnat_s using 1 <;> simp only [ConcreteCategory.comp_apply] <;> rfl
        have hsection :
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) (hU.fromSpec p) (by simpa)
                ((ℱ.restrictAppIso hU.fromSpec V).hom s) =
              eIso.hom (G.presheaf.germ V p hpV s) := by
          convert hnat_s'.symm using 1 <;> rfl
        have hscalar :
            X.presheaf.germ (hU.fromSpec ''ᵁ V) (hU.fromSpec p) (by simpa)
                ((hU.fromSpec.appIso V).inv rV) =
              algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) r := by
          change X.presheaf.germ (hU.fromSpec ''ᵁ V) (hU.fromSpec p) _
              ((hU.fromSpec.appIso V).inv rV) = X.presheaf.germ U (hU.fromSpec p) hp r
          apply (ConcreteCategory.bijective_of_isIso (hU.fromSpec.stalkMap p)).1
          rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
          change (((hU.fromSpec.appIso V).inv ≫ hU.fromSpec.app (hU.fromSpec ''ᵁ V) ≫
              (Spec Γ(X, U)).presheaf.germ
                (hU.fromSpec ⁻¹ᵁ hU.fromSpec ''ᵁ V) p _) rV) =
            ((hU.fromSpec.app U ≫ (Spec Γ(X, U)).presheaf.germ
                (hU.fromSpec ⁻¹ᵁ U) p _) r)
          rw [Scheme.Hom.appIso_inv_app_assoc, hU.fromSpec_app_self]
          simp only [Category.assoc]
          rw [TopCat.Presheaf.germ_res, TopCat.Presheaf.germ_res]
          exact hr.symm
        have hfinal :
            ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) (hU.fromSpec p) (by simpa) (rV • s) =
              r • (show N₂ from eIso.hom (G.presheaf.germ V p hpV s)) := by
          -- Local instance justification (defeq pin): restore the native target-stalk module
          -- structure for the final scalar calculation.
          letI : Module (X.presheaf.stalk (hU.fromSpec p)) N₂ := hXN₂
          change ℱ.presheaf.germ (hU.fromSpec ''ᵁ V) (hU.fromSpec p) _
              ((ℱ.restrictAppIso hU.fromSpec V).hom (rV • s)) =
            (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) r) •
              (show N₂ from eIso.hom (G.presheaf.germ V p hpV s))
          rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
          refine (PresheafOfModules.germ_smul ℱ.val (hU.fromSpec p)
            (hU.fromSpec ''ᵁ V) _ ((hU.fromSpec.appIso V).inv rV)
            ((ℱ.restrictAppIso hU.fromSpec V).hom s)).trans ?_
          exact (congrArg (fun a : X.presheaf.stalk (hU.fromSpec p) ↦
            a • (show N₂ from ℱ.presheaf.germ (hU.fromSpec ''ᵁ V)
              (hU.fromSpec p) _ ((ℱ.restrictAppIso hU.fromSpec V).hom s))) hscalar).trans
            (congrArg (fun m : N₂ ↦
              (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) r) • m) hsection)
        exact hfinal
      exact e₁.trans e₂
    let g := eOut.toLinearMap ∘ₗ f₀ ∘ₗ eIn.toLinearMap
    -- Local instance justification (proof-local temporary data): transport localization across
    -- the source linear equivalence.
    haveI : IsLocalizedModule p.asIdeal.primeCompl (f₀ ∘ₗ eIn.toLinearMap) :=
      IsLocalizedModule.of_linearEquiv_right p.asIdeal.primeCompl f₀ eIn
    -- Local instance justification (proof-local temporary data): transport localization across
    -- the target linear equivalence.
    haveI : IsLocalizedModule p.asIdeal.primeCompl g :=
      IsLocalizedModule.of_linearEquiv p.asIdeal.primeCompl
        (f₀ ∘ₗ eIn.toLinearMap) eOut
    have hgf : g =
        ({ toFun := fun m ↦ ℱ.presheaf.germ U (hU.fromSpec p) hp m
           map_add' := fun a b ↦
             (TopCat.Presheaf.germ ℱ.val.presheaf U (hU.fromSpec p) hp).hom.map_add a b
           map_smul' := fun r m ↦ PresheafOfModules.germ_smul ℱ.val
             (hU.fromSpec p) U hp r m } :
          Γ(ℱ, U) →ₗ[Γ(X, U)]
            (ModuleCat.restrictScalars
              (X.presheaf.germ U (hU.fromSpec p) hp).hom).obj
                (RingedSpace.stalkModuleCat ℱ (hU.fromSpec p))) := by
      apply LinearMap.ext
      intro m
      dsimp only [g, LinearMap.comp_apply]
      change ((Scheme.Modules.restrictStalkNatIso hU.fromSpec p).hom.app ℱ)
          ((RingedSpace.stalkModuleFunctor p).map G.fromTildeΓ
            (tilde.toStalk M₀ p (eIn m))) = ℱ.presheaf.germ U (hU.fromSpec p) hp m
      have hstalk :
          (RingedSpace.stalkModuleFunctor p).map G.fromTildeΓ
              (tilde.toStalk M₀ p (eIn m)) =
            G.presheaf.germ ⊤ p (by simp) (eIn m) := by
        calc
          _ = G.presheaf.germ ⊤ p (by simp)
                (((Scheme.Modules.toPresheaf (Spec (.of Γ(X, U)))).map G.fromTildeΓ).app
                  (Opposite.op ⊤) (tilde.toOpen M₀ ⊤ (eIn m))) := by
              exact TopCat.Presheaf.stalkFunctor_map_germ_apply
                (F := (tilde M₀).presheaf) (G := G.presheaf) ⊤ p (by simp)
                ((Scheme.Modules.toPresheaf (Spec (.of Γ(X, U)))).map G.fromTildeΓ)
                (tilde.toOpen M₀ ⊤ (eIn m))
          _ = _ := by
            change G.presheaf.germ ⊤ p _
                (G.fromTildeΓ.val.app (Opposite.op ⊤) (tilde.toOpen M₀ ⊤ (eIn m))) = _
            have happ : G.fromTildeΓ.val.app (Opposite.op ⊤)
                    (tilde.toOpen M₀ ⊤ (eIn m)) =
                  G.val.map (homOfLE le_rfl).op (eIn m) := by
              change (modulesSpecToSheaf.map G.fromTildeΓ).hom.app (Opposite.op ⊤)
                    (tilde.toOpen ((modulesSpecToSheaf.obj G).presheaf.obj
                      (Opposite.op ⊤)) ⊤ (eIn m)) =
                (modulesSpecToSheaf.obj G).obj.map (homOfLE le_rfl).op (eIn m)
              simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom
                (Scheme.Modules.toOpen_fromTildeΓ_app G ⊤) (eIn m)
            rw [happ]
            exact G.presheaf.germ_res_apply (homOfLE le_rfl) p (by simp) (eIn m)
      rw [hstalk]
      have hnat := ConcreteCategory.congr_hom
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app hU.fromSpec p ℱ (by simp)) (eIn m)
      rw [show ((Scheme.Modules.restrictStalkNatIso hU.fromSpec p).hom.app ℱ)
            (G.presheaf.germ ⊤ p (by simp) (eIn m)) =
          ℱ.presheaf.germ (hU.fromSpec ''ᵁ (⊤ : (Spec (.of Γ(X, U))).Opens))
            (hU.fromSpec p) (by simpa) (eIn m) by
        convert hnat using 1 <;> simp only [ConcreteCategory.comp_apply] <;> rfl]
      let htop : hU.fromSpec ''ᵁ (⊤ : (Spec (.of Γ(X, U))).Opens) = U :=
        hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
      dsimp only [eIn]
      change ℱ.presheaf.germ (hU.fromSpec ''ᵁ
          (⊤ : (Spec (.of Γ(X, U))).Opens)) (hU.fromSpec p) _
          (ℱ.val.presheaf.map (eqToHom htop).op m) =
        ℱ.presheaf.germ U (hU.fromSpec p) hp m
      exact ℱ.presheaf.germ_res_apply (eqToHom htop) (hU.fromSpec p) (by simpa) m
    rw [← hgf]
    infer_instance
  have transportSectionLocalization (z y : X) (hz : z = y)
      (hzU : z ∈ U) (hyU : y ∈ U) (S : Submonoid Γ(X, U))
      (h : IsLocalizedModule S
        ({ toFun := fun m ↦ ℱ.presheaf.germ U z hzU m
           map_add' := fun a b ↦
             (TopCat.Presheaf.germ ℱ.val.presheaf U z hzU).hom.map_add a b
           map_smul' := fun r m ↦ PresheafOfModules.germ_smul ℱ.val z U hzU r m } :
          Γ(ℱ, U) →ₗ[Γ(X, U)]
            (ModuleCat.restrictScalars (X.presheaf.germ U z hzU).hom).obj
              (RingedSpace.stalkModuleCat ℱ z))) :
      IsLocalizedModule S
        ({ toFun := fun m ↦ ℱ.presheaf.germ U y hyU m
           map_add' := fun a b ↦
             (TopCat.Presheaf.germ ℱ.val.presheaf U y hyU).hom.map_add a b
           map_smul' := fun r m ↦ PresheafOfModules.germ_smul ℱ.val y U hyU r m } :
          Γ(ℱ, U) →ₗ[Γ(X, U)]
            (ModuleCat.restrictScalars (X.presheaf.germ U y hyU).hom).obj
              (RingedSpace.stalkModuleCat ℱ y)) := by
    subst y
    exact h
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have hp : hU.fromSpec p = x := by
    simpa only [p] using hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hpU : hU.fromSpec p ∈ U := hp.symm ▸ hxU
  have hfp := transportSectionLocalization (hU.fromSpec p) x hp hpU hxU
    p.asIdeal.primeCompl (sectionToStalk_isLocalized p hpU)
  let f : Γ(ℱ, U) →ₗ[Γ(X, U)]
      (ModuleCat.restrictScalars (X.presheaf.germ U x hxU).hom).obj
        (RingedSpace.stalkModuleCat ℱ x) :=
    { toFun := fun m ↦ ℱ.presheaf.germ U x hxU m
      map_add' := fun a b ↦
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hxU).hom.map_add a b
      map_smul' := fun r m ↦ PresheafOfModules.germ_smul ℱ.val x U hxU r m }
  change IsLocalizedModule p.asIdeal.primeCompl f at hfp
  -- Local instance justification (proof-local temporary data): the chosen point supplies
  -- temporary nonemptiness of the affine open.
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hxU⟩
  let ηU : U := ⟨genericPoint X, hηU⟩
  let q : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ηU
  have hq : hU.fromSpec q = genericPoint X := by
    simpa only [q, ηU] using hU.fromSpec_primeIdealOf ηU
  have hqU : hU.fromSpec q ∈ U := hq.symm ▸ hηU
  have hg := transportSectionLocalization (hU.fromSpec q) (genericPoint X) hq hqU hηU
    q.asIdeal.primeCompl (sectionToStalk_isLocalized q hqU)
  let g : Γ(ℱ, U) →ₗ[Γ(X, U)]
      (ModuleCat.restrictScalars (X.germToFunctionField U).hom).obj
        (RingedSpace.stalkModuleCat ℱ (genericPoint X)) :=
    { toFun := fun m ↦ ℱ.presheaf.germ U (genericPoint X) hηU m
      map_add' := fun a b ↦
        (TopCat.Presheaf.germ ℱ.val.presheaf U (genericPoint X) hηU).hom.map_add a b
      map_smul' := fun r m ↦ PresheafOfModules.germ_smul ℱ.val
        (genericPoint X) U hηU r m }
  change IsLocalizedModule q.asIdeal.primeCompl g at hg
  have hq0 : q = (⊥ : PrimeSpectrum Γ(X, U)) := by
    dsimp only [q, ηU]
    rw [
      hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  have hpq : p.asIdeal.primeCompl ≤ q.asIdeal.primeCompl := by
    rw [hq0]
    intro a ha
    change (a : Γ(X, U)) ∉ (⊥ : Ideal Γ(X, U))
    simpa only [Ideal.mem_bot] using
      (show (a : Γ(X, U)) ≠ 0 from fun ha0 ↦ ha (ha0 ▸ p.asIdeal.zero_mem))
  -- Local instance justification (proof-local temporary data): expose the two already proved
  -- affine localization properties while invoking their canonical comparison map.
  letI : IsLocalizedModule p.asIdeal.primeCompl f := hfp
  letI : IsLocalizedModule q.asIdeal.primeCompl g := hg
  let comparison := IsLocalizedModule.liftOfLE p.asIdeal.primeCompl
    q.asIdeal.primeCompl hpq f g
  have hcomparison : IsLocalizedModule q.asIdeal.primeCompl comparison := inferInstance
  -- Local instance justification (defeq pin): use the canonical section-to-stalk algebra map
  -- when restricting the stalk-to-generic-stalk map to the affine section ring.
  letI stalkAlgebra : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  -- Local instance justification (defeq pin): record compatibility of the affine section,
  -- local-ring, and function-field scalar actions.
  letI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
    functionField_isScalarTower X U ⟨x, hxU⟩
  let Mx := RingedSpace.stalkModuleCat ℱ x
  let Nη := (ModuleCat.restrictScalars
    (algebraMap (X.presheaf.stalk x) X.functionField)).obj
      (RingedSpace.stalkModuleCat ℱ (genericPoint X))
  -- Local instance justification (defeq pin): expose the restricted affine-section scalar
  -- action on the source stalk module.
  letI : Module Γ(X, U) Mx :=
    Module.compHom Mx (algebraMap Γ(X, U) (X.presheaf.stalk x))
  -- Local instance justification (defeq pin): record the canonical source-stalk scalar tower.
  letI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) Mx :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  -- Local instance justification (defeq pin): expose the restricted affine-section scalar
  -- action on the generic stalk module.
  letI : Module Γ(X, U) Nη :=
    Module.compHom (RingedSpace.stalkModuleCat ℱ (genericPoint X))
      (algebraMap Γ(X, U) X.functionField)
  -- Local instance justification (defeq pin): record the scalar tower through the local ring on
  -- the generic stalk module.
  letI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) Nη :=
    .of_algebraMap_smul fun r m ↦ by
      change algebraMap (X.presheaf.stalk x) X.functionField
          (algebraMap Γ(X, U) (X.presheaf.stalk x) r) • m =
        algebraMap Γ(X, U) X.functionField r • m
      rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x) X.functionField]
  let h := (stalkToFunctionField ℱ x).hom
  let hR := h.restrictScalars Γ(X, U)
  have hhf : hR.comp f = g := by
    apply LinearMap.ext
    intro m
    change TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf
        ((genericPoint_spec X).specializes trivial)
          (TopCat.Presheaf.germ ℱ.val.presheaf U x hxU m) =
      TopCat.Presheaf.germ ℱ.val.presheaf U (genericPoint X) hηU m
    simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom
      (TopCat.Presheaf.germ_stalkSpecializes ℱ.val.presheaf hxU
        ((genericPoint_spec X).specializes trivial)) m
  have hcomparison_eq : comparison = hR := by
    apply IsLocalizedModule.ext p.asIdeal.primeCompl f
      (fun s ↦ IsLocalizedModule.map_units g ⟨s, hpq s.2⟩)
    change (IsLocalizedModule.liftOfLE p.asIdeal.primeCompl
      q.asIdeal.primeCompl hpq f g).comp f = hR.comp f
    rw [IsLocalizedModule.liftOfLE_comp]
    exact hhf.symm
  have hR_localized : IsLocalizedModule q.asIdeal.primeCompl hR := by
    rw [← hcomparison_eq]
    exact hcomparison
  -- Local instance justification (proof-local temporary data): expose the completed affine
  -- localization property while changing scalars to the local ring.
  letI : IsLocalizedModule q.asIdeal.primeCompl hR := hR_localized
  have h_map_localized :
      IsLocalizedModule
        (Algebra.algebraMapSubmonoid (X.presheaf.stalk x) q.asIdeal.primeCompl) h := by
    exact IsLocalizedModule.of_restrictScalars q.asIdeal.primeCompl h
  have hsub :
      Algebra.algebraMapSubmonoid (X.presheaf.stalk x) q.asIdeal.primeCompl ≤
        nonZeroDivisors (X.presheaf.stalk x) := by
    rintro a ⟨r, hr, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    have hr0 : r = 0 :=
      germ_injective_of_isIntegral (X := X) x hxU (by
        change (X.presheaf.germ U x hxU).hom r = 0 at hzero
        simpa using hzero)
    rw [hq0] at hr
    exact hr (hr0 ▸ (⊥ : Ideal Γ(X, U)).zero_mem)
  -- Local instance justification (proof-local temporary data): use the standard affine
  -- localization description of the local ring to clear a local denominator.
  letI stalkLocalization : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hdenom : ∀ a : nonZeroDivisors (X.presheaf.stalk x),
      ∃ m : X.presheaf.stalk x,
        m * a ∈ Algebra.algebraMapSubmonoid
          (X.presheaf.stalk x) q.asIdeal.primeCompl := by
    intro a
    obtain ⟨⟨r, s⟩, hrs⟩ :=
      @IsLocalization.surj Γ(X, U) _ p.asIdeal.primeCompl
        (X.presheaf.stalk x) _ stalkAlgebra stalkLocalization a
    have hr0 : r ≠ 0 := by
      intro hr
      have hzero : algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U)) * a = 0 := by
        simpa only [Submonoid.smul_def, Algebra.smul_def, hr, map_zero, mul_comm] using hrs
      have ha0 : (a : X.presheaf.stalk x) = 0 :=
        (mul_eq_zero.mp hzero).resolve_left
          (IsUnit.ne_zero (IsLocalization.map_units (X.presheaf.stalk x) s))
      exact nonZeroDivisors.ne_zero a.2 ha0
    refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk x) s, ?_⟩
    have hrq : r ∈ q.asIdeal.primeCompl := by
      rw [hq0]
      change r ∉ (⊥ : Ideal Γ(X, U))
      exact fun hrbot ↦ hr0 (by simpa using hrbot)
    rw [show algebraMap Γ(X, U) (X.presheaf.stalk x) s * a =
        algebraMap Γ(X, U) (X.presheaf.stalk x) r by
      simpa only [Submonoid.smul_def, Algebra.smul_def, mul_comm] using hrs]
    exact ⟨r, hrq, rfl⟩
  -- Local instance justification (proof-local temporary data): expose the localization at the
  -- image of affine nonzero elements while enlarging to all local non-zero-divisors.
  letI : IsLocalizedModule
      (Algebra.algebraMapSubmonoid (X.presheaf.stalk x) q.asIdeal.primeCompl) h :=
    h_map_localized
  exact IsLocalizedModule.of_exists_mul_mem
    (Algebra.algebraMapSubmonoid (X.presheaf.stalk x) q.asIdeal.primeCompl)
      (nonZeroDivisors (X.presheaf.stalk x)) hsub hdenom h

end AlgebraicGeometry.Scheme.Modules
