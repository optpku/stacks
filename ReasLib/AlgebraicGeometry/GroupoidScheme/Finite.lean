/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteType.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteType.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Isomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Locus.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.AffineBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant
public import ReasLib.RingTheory.FittingIdeal.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Order.Preorder.Finite

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.GroupoidScheme

/-- The orbit of a point under a groupoid scheme with finite source map is finite. -/
lemma finite_orbit {S : Scheme.{u}} (G : GroupoidScheme S) [IsFinite G.s.left]
    (u : G.U.left) :
    (G.t.left '' (G.s.left ⁻¹' ({u} : Set G.U.left))).Finite := by
  exact (G.s.left.finite_preimage_singleton u).image G.t.left

/-- Composing two composable arrow-points keeps the later target in the orbit of the initial
source. -/
lemma mem_orbit_of_composable_points {S : Scheme.{u}} (G : GroupoidScheme S)
    {u v w : G.U.left} {r r' : G.R.left} (hs : G.s.left r = u)
    (ht : G.t.left r = v) (hs' : G.s.left r' = v) (ht' : G.t.left r' = w) :
    w ∈ G.t.left '' (G.s.left ⁻¹' ({u} : Set G.U.left)) := by
  obtain ⟨z, hzfst, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback r' r (hs'.trans ht.symm)
  let e := CategoryTheory.Limits.PreservesPullback.iso (CategoryTheory.Over.forget S) G.s G.t
  let z' : (pullback G.s G.t).left := e.inv z
  have hzfst' : Over.Hom.left (pullback.fst G.s G.t) z' = r' := by
    have hzfst'' :=
      congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_fst
        (CategoryTheory.Over.forget S) G.s G.t) z)
    change Over.Hom.left (pullback.fst G.s G.t) z' = pullback.fst G.s.left G.t.left z at hzfst''
    exact hzfst''.trans hzfst
  have hzsnd' : Over.Hom.left (pullback.snd G.s G.t) z' = r := by
    have hzsnd'' :=
      congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_snd
        (CategoryTheory.Over.forget S) G.s G.t) z)
    change Over.Hom.left (pullback.snd G.s G.t) z' = pullback.snd G.s.left G.t.left z at hzsnd''
    exact hzsnd''.trans hzsnd
  refine ⟨G.c.left z', ?_, ?_⟩
  · have hsource := congrArg Over.Hom.left G.comp_source
    have hs_comp : G.s.left (G.c.left z') = u := by
      have hsource' := congr($(hsource) z')
      change G.s.left (G.c.left z') =
        G.s.left (Over.Hom.left (pullback.snd G.s G.t) z') at hsource'
      calc
        G.s.left (G.c.left z') =
            G.s.left (Over.Hom.left (pullback.snd G.s G.t) z') := hsource'
        _ = G.s.left r := by rw [hzsnd']
        _ = u := hs
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hs_comp
  · have htarget := congrArg Over.Hom.left G.comp_target
    have htarget' := congr($(htarget) z')
    change G.t.left (G.c.left z') =
      G.t.left (Over.Hom.left (pullback.fst G.s G.t) z') at htarget'
    calc
      G.t.left (G.c.left z') =
          G.t.left (Over.Hom.left (pullback.fst G.s G.t) z') := htarget'
      _ = G.t.left r' := by rw [hzfst']
      _ = w := ht'

/-- Distinct points in the same orbit of a groupoid scheme with finite source and target maps
do not specialize from the first point to the second. -/
theorem not_specializes_of_mem_orbit {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left] {u u' : G.U.left}
    (h_ne : u ≠ u') (h_orbit : u' ∈ G.t.left '' (G.s.left ⁻¹' {u})) :
    ¬ u ⤳ u' := by
  classical
  intro huu'
  let strictOrbit : Set G.U.left :=
    {v | v ∈ G.t.left '' (G.s.left ⁻¹' ({u} : Set G.U.left)) ∧ u ⤳ v ∧ v ≠ u}
  have hfinite : strictOrbit.Finite := by
    refine (G.finite_orbit u).subset ?_
    intro v hv
    exact hv.1
  have hu'_mem : u' ∈ strictOrbit := ⟨h_orbit, huu', h_ne.symm⟩
  obtain ⟨v, hvmin⟩ := hfinite.exists_minimal ⟨u', hu'_mem⟩
  rcases hvmin.prop with ⟨hv_orbit, huv, hv_ne⟩
  rcases hv_orbit with ⟨r, hr_mem, ht⟩
  have hs : G.s.left r = u := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hr_mem
  have hsSpecializing : SpecializingMap G.s.left := G.s.left.isClosedMap.specializingMap
  have huv_lift : flip (fun x y : G.U.left ↦ x ⤳ y) v (G.s.left r) := by
    change G.s.left r ⤳ v
    simpa [hs] using huv
  rcases hsSpecializing (a := r) (b := v) huv_lift with ⟨r', hrr', hs'⟩
  let w : G.U.left := G.t.left r'
  have hw_orbit : w ∈ G.t.left '' (G.s.left ⁻¹' ({u} : Set G.U.left)) :=
    G.mem_orbit_of_composable_points hs ht hs' rfl
  have hvw : v ⤳ w := by
    simpa [ht, w] using hrr'.map G.t.left.continuous
  have huw : u ⤳ w := huv.trans hvw
  have hw_ne : w ≠ u := by
    intro hwu
    have hvu' : v ⤳ u := by simpa [hwu] using hvw
    exact hv_ne (huv.antisymm hvu').eq.symm
  have hwv_ne : w ≠ v := by
    intro hwv
    have htarget : G.t.left r = G.t.left r' := by
      simpa [ht, w, hwv]
    have hrr'_eq : r = r' := by
      exact (G.t.left.isDiscrete_preimage_singleton (G.t.left r)).eq_of_specializes hrr'
        (by simp)
        (by simpa [Set.mem_preimage, Set.mem_singleton_iff] using htarget.symm)
    exact hv_ne <| by
      simpa [hs, hs'] using (congrArg G.s.left hrr'_eq).symm
  have hw_mem : w ∈ strictOrbit := ⟨hw_orbit, huw, hw_ne⟩
  have hw_lt : w < v := by
    refine lt_of_le_not_ge hvw ?_
    intro hvw'
    exact hwv_ne (hvw.antisymm hvw').eq.symm
  exact hvmin.not_lt hw_mem hw_lt

/-- If a groupoid arrow has source `u` and target `u'`, then distinctness of the endpoints
prevents `u` from specializing to `u'` when both structure maps are finite. -/
theorem not_specializes_of_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left] {u u' : G.U.left} (h_ne : u ≠ u')
    (r : G.R.left) (hs : G.s.left r = u) (ht : G.t.left r = u') :
    ¬ u ⤳ u' := by
  apply G.not_specializes_of_mem_orbit h_ne
  exact ⟨r, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hs, ht⟩

/-- The Fitting ideals of the source pushforward form a monotone family. -/
lemma sourcePushforwardFittingIdealSheaf_monotone {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] :
    Monotone (fun r : ℕ ↦
      Scheme.fittingIdealSheaf G.s.left.pushforwardStructureModule r) := by
  let F₀ : G.R.left.Modules := SheafOfModules.unit G.R.left.ringCatSheaf
  -- Local instance justification (proof-local temporary data): the finite-source pushforward instances require the standard quasicoherence witness for the structure module.
  letI : F₀.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent G.R.left.ringCatSheaf).prop_of_iso
      (Limits.coproductUniqueIso (fun _ : PUnit ↦ SheafOfModules.unit G.R.left.ringCatSheaf))
      (inferInstanceAs ((SheafOfModules.free (R := G.R.left.ringCatSheaf) PUnit).IsQuasicoherent))
  -- Local instance justification (proof-local temporary data): the unit module is finite type for the duration of the pushforward calculation.
  letI : F₀.IsFiniteType := inferInstance
  let F := G.s.left.pushforwardStructureModule
  -- Local instance justification (proof-local temporary data): finite pushforward supplies finite type for the module whose Fitting ideals are compared.
  letI : F.IsFiniteType := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  -- Local instance justification (proof-local temporary data): finite pushforward supplies quasicoherence for the module whose Fitting ideals are compared.
  letI : F.IsQuasicoherent := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  intro r q hrq
  rw [Scheme.IdealSheafData.le_def]
  intro U
  rw [Scheme.fittingIdealSheaf_ideal, Scheme.fittingIdealSheaf_ideal]
  -- Local instance justification (proof-local temporary data): affine finite sections are used only to invoke monotonicity of module-theoretic Fitting ideals on this chart.
  letI : Module.Finite Γ(G.U.left, U) Γ(F, (U : G.U.left.Opens)) := inferInstance
  simpa using
    (FittingIdeal.monotone (R := Γ(G.U.left, U))
      (M := Γ(F, (U : G.U.left.Opens))) hrq)

/-- The canonical closed filtration attached to the finite source map of a groupoid scheme. -/
noncomputable def sourcePushforwardFittingFiltration {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] :
    ℕ →o Scheme.IdealSheafData G.U.left where
  toFun r := Scheme.fittingIdealSheaf G.s.left.pushforwardStructureModule r
  monotone' := sourcePushforwardFittingIdealSheaf_monotone G

/-- A stage of the source-pushforward Fitting filtration is the corresponding Fitting ideal
sheaf. -/
@[simp]
theorem sourcePushforwardFittingFiltration_apply {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] (r : ℕ) :
    G.sourcePushforwardFittingFiltration r =
      Scheme.fittingIdealSheaf G.s.left.pushforwardStructureModule r := rfl

/-- The zeroth Fitting ideal sheaf of the source pushforward is the zero ideal sheaf. -/
theorem sourcePushforwardFittingZero_eq_bot {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] :
    Scheme.fittingIdealSheaf G.s.left.pushforwardStructureModule 0 = ⊥ := by
  let F₀ : G.R.left.Modules := SheafOfModules.unit G.R.left.ringCatSheaf
  -- Local instance justification (proof-local temporary data): the finite-source pushforward instances require the standard quasicoherence witness for the structure module.
  letI : F₀.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent G.R.left.ringCatSheaf).prop_of_iso
      (Limits.coproductUniqueIso (fun _ : PUnit ↦ SheafOfModules.unit G.R.left.ringCatSheaf))
      (inferInstanceAs ((SheafOfModules.free (R := G.R.left.ringCatSheaf) PUnit).IsQuasicoherent))
  -- Local instance justification (proof-local temporary data): the unit module is finite type for the duration of the zeroth-stage calculation.
  letI : F₀.IsFiniteType := inferInstance
  let F := G.s.left.pushforwardStructureModule
  -- Local instance justification (proof-local temporary data): finite pushforward supplies finite type for the source pushforward in this proof.
  letI : F.IsFiniteType := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  -- Local instance justification (proof-local temporary data): finite pushforward supplies quasicoherence for the source pushforward in this proof.
  letI : F.IsQuasicoherent := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  have hs : G.e.left ≫ G.s.left = 𝟙 G.U.left := by
    simpa using congrArg Over.Hom.left G.identity_source
  apply le_antisymm
  · rw [Scheme.IdealSheafData.le_def]
    intro U
    rw [Scheme.fittingIdealSheaf_ideal]
    -- Local instance justification (proof-local temporary data): affine finite sections are used only for the zeroth Fitting-ideal calculation on this chart.
    letI : Module.Finite Γ(G.U.left, U) Γ(F, (U : G.U.left.Opens)) := inferInstance
    let V : G.R.left.Opens := G.s.left ⁻¹ᵁ (U : G.U.left.Opens)
    let hUe : (U : G.U.left.Opens) ≤ G.e.left ⁻¹ᵁ V := by
      intro x hx
      change G.e.left x ∈ V
      change (G.e.left ≫ G.s.left) x ∈ (U : G.U.left.Opens)
      simpa [hs] using hx
    let eSections :=
      RingedSpace.Module.Sections.Pushforward.sectionIso
        G.s.left.toLRSHom.toShHom (U : G.U.left.Opens) F₀
    let oneSource :
        ((RingedSpace.moduleSectionsRestrictionFunctor
            G.s.left.toLRSHom.toShHom (U : G.U.left.Opens)).obj
          ((RingedSpace.moduleSectionsEvaluationFunctor G.R.left.toSheafedSpace V).obj F₀)) :=
      G.s.left.app (U : G.U.left.Opens) (1 : Γ(G.U.left, (U : G.U.left.Opens)))
    refine le_trans
      (FittingIdeal.zero_le_annihilator
        (R := Γ(G.U.left, U)) (M := Γ(F, (U : G.U.left.Opens)))) ?_
    intro a ha
    have hAnnZero : a = 0 := by
      let x : Γ(F, (U : G.U.left.Opens)) := eSections.hom oneSource
      have hx : a • x = 0 := Module.mem_annihilator.mp ha x
      have hsMapZero : G.s.left.app (U : G.U.left.Opens) a = 0 := by
        have hx' : eSections.inv.hom (a • x) = eSections.inv.hom 0 :=
          congrArg (fun y => eSections.inv.hom y) hx
        have hx'' : a • eSections.inv.hom x = 0 := by
          calc
            a • eSections.inv.hom x = eSections.inv.hom (a • x) := by
              symm
              exact eSections.inv.hom.map_smul a x
            _ = eSections.inv.hom 0 := hx'
            _ = 0 := by simp
        have hrestrict :
            (a • eSections.inv.hom x :
                ((RingedSpace.moduleSectionsRestrictionFunctor
                    G.s.left.toLRSHom.toShHom (U : G.U.left.Opens)).obj
                  ((RingedSpace.moduleSectionsEvaluationFunctor
                      G.R.left.toSheafedSpace V).obj F₀))) =
              (G.s.left.app (U : G.U.left.Opens) a) •
                (show
                  ((RingedSpace.moduleSectionsEvaluationFunctor
                      G.R.left.toSheafedSpace V).obj F₀) from eSections.inv.hom x) :=
          ModuleCat.restrictScalars.smul_def
            (G.s.left.app (U : G.U.left.Opens)).hom a (eSections.inv.hom x)
        have hx''' :
            (G.s.left.app (U : G.U.left.Opens) a) •
                (show
                  ((RingedSpace.moduleSectionsEvaluationFunctor
                      G.R.left.toSheafedSpace V).obj F₀) from eSections.inv.hom x) = 0 := by
          calc
            (G.s.left.app (U : G.U.left.Opens) a) •
                (show
                  ((RingedSpace.moduleSectionsEvaluationFunctor
                      G.R.left.toSheafedSpace V).obj F₀) from eSections.inv.hom x) =
                a • eSections.inv.hom x := by
                  symm
                  exact hrestrict
            _ = 0 := hx''
        have hx'''Raw := congrArg
          (fun y :
              ((RingedSpace.moduleSectionsEvaluationFunctor
                  G.R.left.toSheafedSpace V).obj F₀) =>
            (show Γ(G.R.left, V) from y)) hx'''
        have hDistinguished :
            (show Γ(G.R.left, V) from eSections.inv.hom x) = 1 := by
          simp [x, oneSource]
        have hsMapZeroMul :
            (G.s.left.app (U : G.U.left.Opens) a : Γ(G.R.left, V)) •
              (1 : Γ(G.R.left, V)) = 0 := by
          calc
            (G.s.left.app (U : G.U.left.Opens) a : Γ(G.R.left, V)) •
                (1 : Γ(G.R.left, V)) =
              (G.s.left.app (U : G.U.left.Opens) a : Γ(G.R.left, V)) •
                (show Γ(G.R.left, V) from eSections.inv.hom x) := by
                  rw [hDistinguished]
            _ = 0 := hx'''Raw
        have hsMapZero' :
            (G.s.left.app (U : G.U.left.Opens) a : Γ(G.R.left, V)) = 0 := by
          simpa [smul_eq_mul, mul_one] using hsMapZeroMul
        exact hsMapZero'
      let eU : (U : G.U.left.Opens) ≤ (𝟙 G.U.left) ⁻¹ᵁ (U : G.U.left.Opens) := by
        simp
      have hUid :
          (U : G.U.left.Opens) ≤ (G.e.left ≫ G.s.left) ⁻¹ᵁ (U : G.U.left.Opens) := by
        simpa [hs] using eU
      have hIdSections :
          Scheme.Hom.sectionsMapAlong (G.e.left ≫ G.s.left)
            (U : G.U.left.Opens) (U : G.U.left.Opens) hUid =
            RingHom.id Γ(G.U.left, (U : G.U.left.Opens)) := by
        have hId :
            Scheme.Hom.sectionsMapAlong (𝟙 G.U.left)
              (U : G.U.left.Opens) (U : G.U.left.Opens) eU =
              RingHom.id Γ(G.U.left, (U : G.U.left.Opens)) := by
          ext r
          simp only [Scheme.Hom.sectionsMapAlong, Scheme.Hom.appLE,
            Scheme.Hom.id_app, Category.id_comp, CommRingCat.comp_apply,
            CommRingCat.id_apply]
          have he : (homOfLE eU).op = 𝟙 (Opposite.op (U : G.U.left.Opens)) := Subsingleton.elim _ _
          rw [he]
          change (G.U.left.presheaf.map (𝟙 (Opposite.op (U : G.U.left.Opens)))).hom r = r
          simpa only [ConcreteCategory.id_apply] using DFunLike.congr_fun
            (congrArg CommRingCat.Hom.hom
              (G.U.left.presheaf.map_id (Opposite.op (U : G.U.left.Opens)))) r
        simpa [hs] using hId
      have hCompApply :
          (G.e.left.appLE V (U : G.U.left.Opens) hUe).hom
              (G.s.left.app (U : G.U.left.Opens) a) =
            (Scheme.Hom.sectionsMapAlong (G.e.left ≫ G.s.left)
              (U : G.U.left.Opens) (U : G.U.left.Opens) hUid) a := by
        have hComp :
            CommRingCat.ofHom
                (Scheme.Hom.sectionsMapAlong G.s.left (U : G.U.left.Opens) V le_rfl) ≫
              CommRingCat.ofHom
                (Scheme.Hom.sectionsMapAlong G.e.left V (U : G.U.left.Opens) hUe) =
            CommRingCat.ofHom
              (Scheme.Hom.sectionsMapAlong (G.e.left ≫ G.s.left)
                (U : G.U.left.Opens) (U : G.U.left.Opens) hUid) :=
          Scheme.Hom.sectionsMapAlong_comp
            (f := G.e.left) (g := G.s.left)
            (W := (U : G.U.left.Opens)) (V := V) (U := (U : G.U.left.Opens))
            (hV := le_rfl) (hU := hUe)
        have hCompRaw := congrArg
          (fun f : Γ(G.U.left, (U : G.U.left.Opens)) ⟶
              Γ(G.U.left, (U : G.U.left.Opens)) => f.hom a) hComp
        simpa [V, hUe, hUid, Scheme.Hom.sectionsMapAlong, Scheme.Hom.appLE] using hCompRaw
      calc
        a = (Scheme.Hom.sectionsMapAlong (G.e.left ≫ G.s.left)
              (U : G.U.left.Opens) (U : G.U.left.Opens) hUid) a := by
            simpa [hIdSections]
        _ = (G.e.left.appLE V (U : G.U.left.Opens) hUe).hom
              (G.s.left.app (U : G.U.left.Opens) a) := hCompApply.symm
        _ = 0 := by simpa [hsMapZero]
    exact hAnnZero
  · exact bot_le

/-- The source-pushforward Fitting filtration starts at the zero ideal sheaf. -/
theorem sourcePushforwardFittingFiltration_zero {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] :
    G.sourcePushforwardFittingFiltration 0 = ⊥ :=
  sourcePushforwardFittingZero_eq_bot G

/-- Pulling the source pushforward structure module back along the target or source map gives
isomorphic module sheaves on the arrow scheme. -/
theorem sourcePushforwardPullbacks_isIsomorphic
    {S : Scheme.{u}} (G : GroupoidScheme S) [IsFinite G.s.left]
    [IsFinite G.t.left] :
    IsIsomorphic
      (((Scheme.Modules.pullback G.t.left).obj G.s.left.pushforwardStructureModule) :
        G.R.left.Modules)
      (((Scheme.Modules.pullback G.s.left).obj G.s.left.pushforwardStructureModule) :
        G.R.left.Modules) := by
  let F₀ : G.R.left.Modules := SheafOfModules.unit G.R.left.ringCatSheaf
  -- Local instance justification (proof-local temporary data): affine base change requires quasicoherence of the structure module being pushed forward.
  letI : F₀.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent G.R.left.ringCatSheaf).prop_of_iso
      (Limits.coproductUniqueIso (fun _ : PUnit ↦ SheafOfModules.unit G.R.left.ringCatSheaf))
      (inferInstanceAs ((SheafOfModules.free (R := G.R.left.ringCatSheaf) PUnit).IsQuasicoherent))
  let P : (pullback G.s G.t).left.Modules :=
    SheafOfModules.unit (pullback G.s G.t).left.ringCatSheaf
  have hProjection :
      IsPullback (Over.Hom.left (pullback.fst G.s G.t))
        (Over.Hom.left (pullback.snd G.s G.t)) G.s.left G.t.left := by
    simpa using G.fstSndIsPullback.map (Over.forget S)
  have hComp :
      IsPullback G.c.left (Over.Hom.left (pullback.snd G.s G.t)) G.s.left G.s.left := by
    simpa using G.compSndIsPullback.map (Over.forget S)
  rcases
      (Scheme.affineBaseChange_pushforward_isomorphic
        (Over.Hom.left (pullback.fst G.s G.t))
        (Over.Hom.left (pullback.snd G.s G.t))
        G.s.left G.t.left hProjection F₀) with
    ⟨eTarget⟩
  rcases
      (Scheme.affineBaseChange_pushforward_isomorphic
        G.c.left
        (Over.Hom.left (pullback.snd G.s G.t))
        G.s.left G.s.left hComp F₀) with
    ⟨eSource⟩
  let eUnitTarget :
      ((Scheme.Modules.pullback (Over.Hom.left (pullback.fst G.s G.t))).obj F₀) ≅ P := by
    exact
      (Scheme.Modules.pullback (Over.Hom.left (pullback.fst G.s G.t))).mapIso
          (RingedSpace.unitIsoTensorUnit G.R.left.toRingedSpace) ≪≫
        Scheme.Modules.pullbackUnitIso (Over.Hom.left (pullback.fst G.s G.t)) ≪≫
          (RingedSpace.unitIsoTensorUnit (pullback G.s G.t).left.toRingedSpace).symm
  let eUnitSource : ((Scheme.Modules.pullback G.c.left).obj F₀) ≅ P := by
    exact
      (Scheme.Modules.pullback G.c.left).mapIso
          (RingedSpace.unitIsoTensorUnit G.R.left.toRingedSpace) ≪≫
        Scheme.Modules.pullbackUnitIso G.c.left ≪≫
          (RingedSpace.unitIsoTensorUnit (pullback G.s G.t).left.toRingedSpace).symm
  let eTarget' :
      ((Scheme.Modules.pullback G.t.left).obj G.s.left.pushforwardStructureModule) ≅
        ((Scheme.Modules.pushforward (Over.Hom.left (pullback.snd G.s G.t))).obj P) :=
    eTarget.trans <|
      (Scheme.Modules.pushforward (Over.Hom.left (pullback.snd G.s G.t))).mapIso
        eUnitTarget
  let eSource' :
      ((Scheme.Modules.pullback G.s.left).obj G.s.left.pushforwardStructureModule) ≅
        ((Scheme.Modules.pushforward (Over.Hom.left (pullback.snd G.s G.t))).obj P) :=
    eSource.trans <|
      (Scheme.Modules.pushforward (Over.Hom.left (pullback.snd G.s G.t))).mapIso
        eUnitSource
  exact ⟨eTarget'.trans eSource'.symm⟩

/-- The target and source pullbacks of every source-pushforward Fitting ideal sheaf agree. -/
theorem sourcePushforwardFittingIdealSheaf_comap_target_eq_comap_source
    {S : Scheme.{u}} (G : GroupoidScheme S) [IsFinite G.s.left]
    [IsFinite G.t.left] (r : ℕ) :
    (Scheme.fittingIdealSheaf G.s.left.pushforwardStructureModule r).comap G.t.left =
      (Scheme.fittingIdealSheaf G.s.left.pushforwardStructureModule r).comap G.s.left := by
  let F₀ : G.R.left.Modules := SheafOfModules.unit G.R.left.ringCatSheaf
  -- Local instance justification (proof-local temporary data): the finite-source pushforward instances require the standard quasicoherence witness for the structure module.
  letI : F₀.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent G.R.left.ringCatSheaf).prop_of_iso
      (Limits.coproductUniqueIso (fun _ : PUnit ↦ SheafOfModules.unit G.R.left.ringCatSheaf))
      (inferInstanceAs ((SheafOfModules.free (R := G.R.left.ringCatSheaf) PUnit).IsQuasicoherent))
  -- Local instance justification (proof-local temporary data): the unit module is finite type for the pullback comparison calculation.
  letI : F₀.IsFiniteType := inferInstance
  let F := G.s.left.pushforwardStructureModule
  -- Local instance justification (proof-local temporary data): finite pushforward supplies finite type before applying Fitting-ideal base change.
  letI : F.IsFiniteType := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  -- Local instance justification (proof-local temporary data): finite pushforward supplies quasicoherence before applying Fitting-ideal base change.
  letI : F.IsQuasicoherent := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  let Ft : G.R.left.Modules := (Scheme.Modules.pullback G.t.left).obj F
  -- Local instance justification (proof-local temporary data): pullback preserves finite type for the target-pulled module in this comparison.
  letI : Ft.IsFiniteType := by
    dsimp [Ft]
    infer_instance
  -- Local instance justification (proof-local temporary data): pullback preserves quasicoherence for the target-pulled module in this comparison.
  letI : Ft.IsQuasicoherent := by
    dsimp [Ft]
    infer_instance
  rw [Scheme.fittingIdealSheaf_pullback, Scheme.fittingIdealSheaf_pullback]
  rcases
      sourcePushforwardPullbacks_isIsomorphic G
    with ⟨e⟩
  simpa [F, Ft] using Scheme.fittingIdealSheaf_eq_of_iso Ft _ e r

/-- Every stage of the source-pushforward Fitting filtration is invariant under the groupoid. -/
theorem sourcePushforwardFittingFiltration_isClosedInvariant {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] [IsFinite G.t.left] (r : ℕ) :
    G.toPreRelation.IsClosedInvariant (G.sourcePushforwardFittingFiltration r) := by
  rw [Scheme.PreRelation.isClosedInvariant_iff]
  rw [GroupoidScheme.toPreRelation_t, GroupoidScheme.toPreRelation_s]
  exact sourcePushforwardFittingIdealSheaf_comap_target_eq_comap_source G r

/-- The supports of all stages of the source-pushforward Fitting filtration have empty
intersection. -/
theorem iInter_support_sourcePushforwardFittingFiltration_eq_empty {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] :
    (⋂ r, ((G.sourcePushforwardFittingFiltration r).support : Set G.U.left)) =
      (∅ : Set G.U.left) := by
  let F₀ : G.R.left.Modules := SheafOfModules.unit G.R.left.ringCatSheaf
  -- Local instance justification (proof-local temporary data): the empty-intersection theorem requires the standard quasicoherence witness for the structure module.
  letI : F₀.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent G.R.left.ringCatSheaf).prop_of_iso
      (Limits.coproductUniqueIso (fun _ : PUnit ↦ SheafOfModules.unit G.R.left.ringCatSheaf))
      (inferInstanceAs ((SheafOfModules.free (R := G.R.left.ringCatSheaf) PUnit).IsQuasicoherent))
  -- Local instance justification (proof-local temporary data): the unit module is finite type for this Fitting-support calculation.
  letI : F₀.IsFiniteType := inferInstance
  let F := G.s.left.pushforwardStructureModule
  -- Local instance justification (proof-local temporary data): finite pushforward supplies finite type for the Fitting-support theorem.
  letI : F.IsFiniteType := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  -- Local instance justification (proof-local temporary data): finite pushforward supplies quasicoherence for the Fitting-support theorem.
  letI : F.IsQuasicoherent := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  simpa [sourcePushforwardFittingFiltration, F] using
    Scheme.iInter_support_fittingIdealSheaf_eq_empty F

/-- Over the locally closed difference between consecutive source-pushforward Fitting stages,
the pulled-back source map is finite locally free of the corresponding positive rank. -/
theorem sourcePushforwardRankStratum_isFiniteLocallyFreeOfRank {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] [IsFinite G.t.left] (r : ℕ) :
    IsFiniteLocallyFreeOfRank
      (pullback.snd G.s.left
        ((((Scheme.fittingIdealSheaf G.s.left.pushforwardStructureModule (r + 1)).comap
            (Scheme.fittingIdealSheaf G.s.left.pushforwardStructureModule r).subschemeι).openComplement).ι ≫
          (Scheme.fittingIdealSheaf G.s.left.pushforwardStructureModule r).subschemeι))
      (r + 1) := by
  let F₀ : G.R.left.Modules := SheafOfModules.unit G.R.left.ringCatSheaf
  -- Local instance justification (proof-local temporary data): affine base change requires quasicoherence of the structure module being pushed forward.
  letI : F₀.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent G.R.left.ringCatSheaf).prop_of_iso
      (Limits.coproductUniqueIso (fun _ : PUnit ↦ SheafOfModules.unit G.R.left.ringCatSheaf))
      (inferInstanceAs ((SheafOfModules.free (R := G.R.left.ringCatSheaf) PUnit).IsQuasicoherent))
  -- Local instance justification (proof-local temporary data): the unit module is finite type for the rank-stratum calculation.
  letI : F₀.IsFiniteType := inferInstance
  let F := G.s.left.pushforwardStructureModule
  -- Local instance justification (proof-local temporary data): finite pushforward supplies finite type for the rank-locus theorem.
  letI : F.IsFiniteType := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  -- Local instance justification (proof-local temporary data): finite pushforward supplies quasicoherence for the rank-locus theorem.
  letI : F.IsQuasicoherent := by
    dsimp [F, Scheme.Hom.pushforwardStructureModule]
    infer_instance
  let g := Scheme.fittingRankLocusι F (r + 1)
  have hCanonical : IsFiniteLocallyFreeOfRank (pullback.snd G.s.left g) (r + 1) := by
    have hModuleRank :
        SheafOfModules.IsFiniteLocallyFreeOfRank (r + 1)
          ((Scheme.Modules.pullback g).obj F) := by
      exact
        (Scheme.fittingRankLocus_nonempty_over_hom_iff_isFiniteLocallyFreeOfRank
          g F (r + 1)).2.mp ⟨𝟙 _⟩
    rcases
        (Scheme.affineBaseChange_pushforward_isomorphic
          (pullback.fst G.s.left g)
          (pullback.snd G.s.left g)
          G.s.left g (IsPullback.of_hasPullback G.s.left g) F₀) with
      ⟨eBaseChange⟩
    let eUnit :
        ((Scheme.Modules.pullback (pullback.fst G.s.left g)).obj F₀) ≅
          SheafOfModules.unit (pullback G.s.left g).ringCatSheaf := by
      exact
        (Scheme.Modules.pullback (pullback.fst G.s.left g)).mapIso
            (RingedSpace.unitIsoTensorUnit G.R.left.toRingedSpace) ≪≫
          Scheme.Modules.pullbackUnitIso (pullback.fst G.s.left g) ≪≫
            (RingedSpace.unitIsoTensorUnit (pullback G.s.left g).toRingedSpace).symm
    let ePushforward :
        ((Scheme.Modules.pullback g).obj F) ≅
          (pullback.snd G.s.left g).pushforwardStructureModule :=
      eBaseChange.trans <|
        (Scheme.Modules.pushforward (pullback.snd G.s.left g)).mapIso eUnit
    -- Local instance justification (proof-local temporary data): install the rank result on the pulled-back module only while transporting it through base change.
    letI :
        SheafOfModules.IsFiniteLocallyFreeOfRank (r + 1)
          ((Scheme.Modules.pullback g).obj F) := hModuleRank
    -- Local instance justification (proof-local temporary data): transport fixed rank across the base-change isomorphism to the pushforward structure module.
    letI :
        Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1)
          (pullback.snd G.s.left g).pushforwardStructureModule :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso ePushforward
    let hFiniteLocallyFree : IsFiniteLocallyFree (pullback.snd G.s.left g) :=
      { toIsAffineHom := inferInstance
        pushforward_isFiniteLocallyFree :=
          Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
            (r + 1) (pullback.snd G.s.left g).pushforwardStructureModule }
    exact
      { toIsFiniteLocallyFree := hFiniteLocallyFree
        pushforward_isFiniteLocallyFreeOfRank := inferInstance }
  change IsFiniteLocallyFreeOfRank
      (pullback.snd G.s.left
        ((((Scheme.fittingIdealSheaf F r).subschemeι ⁻¹ᵁ
            Scheme.fittingOpenComplement F (r + 1))).ι ≫
          (Scheme.fittingIdealSheaf F r).subschemeι))
      (r + 1) at hCanonical
  have hopen :
      (Scheme.fittingIdealSheaf F r).subschemeι ⁻¹ᵁ Scheme.fittingOpenComplement F (r + 1) =
        ((Scheme.fittingIdealSheaf F (r + 1)).comap
          (Scheme.fittingIdealSheaf F r).subschemeι).openComplement := by
    ext x
    simp [Scheme.fittingOpenComplement, Scheme.IdealSheafData.openComplement,
      Scheme.IdealSheafData.support_comap, Set.preimage_compl]
  rw [hopen] at hCanonical
  simpa using hCanonical

/-- Consecutive stages of the source-pushforward Fitting filtration have source pullback finite
locally free of the corresponding positive rank. -/
theorem sourcePushforwardFittingFiltration_rankStratum {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] [IsFinite G.t.left] (r : ℕ) :
    IsFiniteLocallyFreeOfRank
      (pullback.snd G.s.left
        ((((G.sourcePushforwardFittingFiltration (r + 1)).comap
            (G.sourcePushforwardFittingFiltration r).subschemeι).openComplement).ι ≫
          (G.sourcePushforwardFittingFiltration r).subschemeι))
      (r + 1) := by
  simpa using sourcePushforwardRankStratum_isFiniteLocallyFreeOfRank G r

/-- A groupoid scheme with finite source and target maps has an invariant closed Fitting
filtration whose successive source strata have their corresponding positive ranks. -/
theorem exists_invariantRankStratification {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left] :
    ∃ Z : ℕ →o Scheme.IdealSheafData G.U.left,
      Z 0 = ⊥ ∧
      (∀ r, G.toPreRelation.IsClosedInvariant (Z r)) ∧
      (⋂ r, ((Z r).support : Set G.U.left)) = (∅ : Set G.U.left) ∧
      ∀ r, IsFiniteLocallyFreeOfRank
        (pullback.snd G.s.left
          (((Z (r + 1)).comap (Z r).subschemeι).openComplement.ι ≫
            (Z r).subschemeι))
        (r + 1) := by
  exact ⟨G.sourcePushforwardFittingFiltration,
    G.sourcePushforwardFittingFiltration_zero,
    G.sourcePushforwardFittingFiltration_isClosedInvariant,
    G.iInter_support_sourcePushforwardFittingFiltration_eq_empty,
    G.sourcePushforwardFittingFiltration_rankStratum⟩

end AlgebraicGeometry.GroupoidScheme
