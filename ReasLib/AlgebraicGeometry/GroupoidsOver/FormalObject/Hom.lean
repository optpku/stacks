/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Basic
public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Hom
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Morphisms of formal objects

Compatible stage maps determine morphisms of formal objects. Their maps on
complete local bases are reconstructed from the induced maps on all quotients.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
  {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, v} (Over S)}

/-- A morphism of formal objects is a natural transformation of their stage functors. -/
abbrev Hom (ξ η : FormalObject X) : Type v := ξ.toFunctor ⟶ η.toFunctor

/-- Construct a morphism from stage maps commuting with successor transitions. -/
def Hom.ofStages {ξ η : FormalObject X} (app : ∀ n, ξ.objects n ⟶ η.objects n)
    (naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n) : Hom ξ η :=
  NatTrans.ofSequence app (by
    intro n
    dsimp only [toFunctor, Functor.ofSequence]
    rw [Functor.OfSequence.map_le_succ, Functor.OfSequence.map_le_succ]
    exact naturality n)

/-- The map of truncated spectra over the base scheme induced by a stage map. -/
def Hom.stageOverMap {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    ξ.base.stageOver n ⟶ η.base.stageOver n :=
  eqToHom (ξ.over_obj n).symm ≫ X.p.map (a.app n) ≫ eqToHom (η.over_obj n)

/-- The quotient ring homomorphism dual to the map of truncated spectra. -/
def Hom.quotientHom {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    η.base.truncationRing n →+* ξ.base.truncationRing n :=
  CommRingCat.Hom.hom <|
    (Scheme.ΓSpecIso (η.base.truncationRing n)).inv ≫ (a.stageOverMap n).left.appTop ≫
      (Scheme.ΓSpecIso (ξ.base.truncationRing n)).hom

omit [IsLocallyNoetherian S] in
/-- The quotient homomorphism recovers the original map of truncated spectra. -/
theorem Hom.quotientHom_spec {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (a.quotientHom n)) = (a.stageOverMap n).left := by
  obtain ⟨f, hf⟩ := Spec.map_surjective (a.stageOverMap n).left
  have h : CommRingCat.ofHom (a.quotientHom n) = f := by
    simp only [Hom.quotientHom, ← hf, CommRingCat.ofHom_hom]
    exact (congrArg ((Scheme.ΓSpecIso (η.base.truncationRing n)).inv ≫ ·)
      (Scheme.ΓSpecIso_naturality f)).trans (Iso.inv_hom_id_assoc _ f)
  rw [h, hf]

omit [IsLocallyNoetherian S] in
/-- The induced maps over `S` commute with successive truncations. -/
theorem Hom.stageOverMap_naturality {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    ξ.base.stageHom n ≫ a.stageOverMap (n + 1) =
      a.stageOverMap n ≫ η.base.stageHom n := by
  letI := ξ.over_step n
  letI := η.over_step n
  have h := a.naturality (homOfLE (Nat.le_succ n))
  dsimp only [toFunctor, Functor.ofSequence] at h
  rw [Functor.OfSequence.map_le_succ, Functor.OfSequence.map_le_succ] at h
  have hξ : ξ.base.stageHom n = eqToHom (ξ.over_obj n).symm ≫
      X.p.map (ξ.step n) ≫ eqToHom (ξ.over_obj (n + 1)) :=
    IsHomLift.fac X.p (ξ.base.stageHom n) (ξ.step n)
  have hη : η.base.stageHom n = eqToHom (η.over_obj n).symm ≫
      X.p.map (η.step n) ≫ eqToHom (η.over_obj (n + 1)) :=
    IsHomLift.fac X.p (η.base.stageHom n) (η.step n)
  rw [hξ, hη]
  simpa only [Hom.stageOverMap, toFunctor, Functor.ofSequence, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Functor.map_comp] using
    congrArg (fun f ↦ eqToHom (ξ.over_obj n).symm ≫ X.p.map f ≫
      eqToHom (η.over_obj (n + 1))) h

-- This instance-free proof keeps the original type of `Hom.baseRingHom`.
omit [IsLocallyNoetherian S] in
private theorem quotientHom_naturality_aux {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    (Ideal.Quotient.factorPow (maximalIdeal ξ.base.carrier) (Nat.le_succ (n + 1))).comp
        (a.quotientHom (n + 1)) =
      (a.quotientHom n).comp
        (Ideal.Quotient.factorPow (maximalIdeal η.base.carrier) (Nat.le_succ (n + 1))) :=
  by
    suffices h : CommRingCat.ofHom
        ((Ideal.Quotient.factorPow (maximalIdeal ξ.base.carrier)
          (Nat.le_succ (n + 1))).comp (a.quotientHom (n + 1))) =
        CommRingCat.ofHom ((a.quotientHom n).comp
          (Ideal.Quotient.factorPow (maximalIdeal η.base.carrier)
            (Nat.le_succ (n + 1)))) by
      exact congrArg CommRingCat.Hom.hom h
    apply Spec.map_injective
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Hom.quotientHom_spec]
    exact congrArg Over.Hom.left (a.stageOverMap_naturality n)

/-- The induced quotient homomorphisms commute with successive quotient projections. -/
theorem Hom.quotientHom_naturality {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    (Ideal.Quotient.factorPow (maximalIdeal ξ.base.carrier) (Nat.le_succ (n + 1))).comp
        (a.quotientHom (n + 1)) =
      (a.quotientHom n).comp
        (Ideal.Quotient.factorPow (maximalIdeal η.base.carrier) (Nat.le_succ (n + 1))) :=
  quotientHom_naturality_aux a n

omit [IsLocallyNoetherian S] in
/-- The ring homomorphism on complete local bases reconstructed from the stage maps. -/
def Hom.baseRingHom {ξ η : FormalObject X} (a : Hom ξ η) :
    η.base.carrier →+* ξ.base.carrier :=
  let completionQuotientHom :
      (n : ℕ) → η.base.carrier →+* ξ.base.carrier ⧸ maximalIdeal ξ.base.carrier ^ n
    | 0 =>
      { toFun := fun _ ↦ 0
        map_zero' := rfl
        map_one' := by
          symm
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          simp
        map_add' := fun _ _ ↦ (zero_add 0).symm
        map_mul' := fun _ _ ↦ (zero_mul 0).symm }
    | n + 1 => (a.quotientHom n).comp
        (Ideal.Quotient.mk (maximalIdeal η.base.carrier ^ (n + 1)))
  (AdicCompletion.ofAlgEquiv (maximalIdeal ξ.base.carrier)).symm.toRingHom.comp
    (AdicCompletion.liftRingHom (maximalIdeal ξ.base.carrier) completionQuotientHom
      (by
        intro m n hmn
        induction hmn with
        | refl =>
            simp [Ideal.Quotient.factorPow]
        | @step n hmn ih =>
            have hs : (Ideal.Quotient.factorPow (maximalIdeal ξ.base.carrier)
                (Nat.le_succ n)).comp (completionQuotientHom (n + 1)) =
                completionQuotientHom n := by
              cases n with
              | zero =>
                  ext x
                  letI : Subsingleton (ξ.base.carrier ⧸ maximalIdeal ξ.base.carrier ^ 0) :=
                    Ideal.Quotient.subsingleton_iff.mpr (by simp)
                  exact Subsingleton.elim _ _
              | succ n =>
                  ext x
                  exact RingHom.congr_fun (quotientHom_naturality_aux a n)
                    (Ideal.Quotient.mk (maximalIdeal η.base.carrier ^ (n + 2)) x)
            rw [← hs] at ih
            simpa only [← RingHom.comp_assoc, Ideal.Quotient.factorPow,
              Ideal.Quotient.factor_comp] using ih))

/-- Reducing the reconstructed homomorphism recovers each positive quotient map. -/
theorem Hom.baseRingHom_mk {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    (Ideal.Quotient.mk (maximalIdeal ξ.base.carrier ^ (n + 1))).comp a.baseRingHom =
      (a.quotientHom n).comp
        (Ideal.Quotient.mk (maximalIdeal η.base.carrier ^ (n + 1))) := by
  ext x
  dsimp only [Hom.baseRingHom, RingHom.comp_apply]
  change Ideal.Quotient.mk _
    ((AdicCompletion.ofAlgEquiv (maximalIdeal ξ.base.carrier)).symm _) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm]
  simp [AdicCompletion.liftRingHom, AdicCompletion.evalₐ, AdicCompletion.eval]

/-- The reconstructed homomorphism of complete local rings is local. -/
theorem Hom.baseRingHom_isLocalHom {ξ η : FormalObject X} (a : Hom ξ η) :
    IsLocalHom a.baseRingHom := by
  classical
  refine ⟨fun x hx ↦ ?_⟩
  by_contra h
  have hz : Ideal.Quotient.mk (maximalIdeal η.base.carrier ^ (0 + 1)) x = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa using (show x ∈ maximalIdeal η.base.carrier from h)
  have hm := RingHom.congr_fun (a.baseRingHom_mk 0) x
  simp only [RingHom.comp_apply, hz, map_zero] at hm
  have hmem : a.baseRingHom x ∈ maximalIdeal ξ.base.carrier := by
    simpa using Ideal.Quotient.eq_zero_iff_mem.mp hm
  exact hmem hx

omit [IsLocallyNoetherian S] in
/-- Maps from a local spectrum are determined by positive truncations when the ring is
separated for its maximal-adic topology. -/
private theorem hom_ext_of_truncations {R : Type u} [CommRing R] [IsLocalRing R]
    [IsHausdorff (maximalIdeal R) R] {Y : Scheme.{u}}
    (f g : Spec (CommRingCat.of R) ⟶ Y)
    (h : ∀ n : ℕ, Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) ≫ f =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) ≫ g) : f = g := by
  have hzero : Spec.map (CommRingCat.ofHom (residue R)) ≫ f =
      Spec.map (CommRingCat.ofHom (residue R)) ≫ g := by
    let r : R ⧸ maximalIdeal R ^ (0 + 1) →+* ResidueField R :=
      Ideal.Quotient.factor (by simp)
    have hq : CommRingCat.ofHom (residue R) =
        CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) ≫
          CommRingCat.ofHom r := by
      rfl
    rw [hq, Spec.map_comp, Category.assoc, h 0, Category.assoc]
  letI : IsLocalHom (CommRingCat.ofHom (residue R)).hom :=
    inferInstanceAs (IsLocalHom (residue R))
  have hclosed : f (closedPoint R) = g (closedPoint R) := by
    have hp := congrArg (fun t ↦ t (closedPoint (ResidueField R))) hzero
    have hpt : Spec.map (CommRingCat.ofHom (residue R))
        (closedPoint (ResidueField R)) = closedPoint R := Spec_closedPoint
    simpa only [Scheme.Hom.comp_apply, hpt] using hp
  obtain ⟨U, hU, hmem, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f (closedPoint R) ∈ (⊤ : Y.Opens) from trivial)
  have hfU : f ⁻¹ᵁ U = ⊤ := closed_point_mem_iff.mp hmem
  have hgU : g ⁻¹ᵁ U = ⊤ := by
    apply closed_point_mem_iff.mp
    change g (closedPoint R) ∈ U
    rwa [← hclosed]
  let F := IsOpenImmersion.lift U.ι f
    (by simpa [Set.range_subset_iff] using fun x hx ↦ hfU.ge hx)
  let G := IsOpenImmersion.lift U.ι g
    (by simpa [Set.range_subset_iff] using fun x hx ↦ hgU.ge hx)
  have hstage (n : ℕ) :
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) ≫ F =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) ≫ G := by
    apply (cancel_mono U.ι).mp
    simpa only [Category.assoc, F, G, IsOpenImmersion.lift_fac] using h n
  have he : Spec.preimage (F ≫ hU.isoSpec.hom) =
      Spec.preimage (G ≫ hU.isoSpec.hom) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply AdicCompletion.of_injective (maximalIdeal R) R
    apply AdicCompletion.ext_evalₐ
    intro n
    simp only [AdicCompletion.evalₐ_of]
    have hn : Spec.preimage (F ≫ hU.isoSpec.hom) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) =
        Spec.preimage (G ≫ hU.isoSpec.hom) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) := by
      apply Spec.map_injective
      simp only [Spec.map_comp, Spec.map_preimage]
      simpa only [Category.assoc] using
        congrArg (fun t ↦ t ≫ hU.isoSpec.hom) (hstage n)
    have hx := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hn) x
    exact congrArg (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ n)) hx
  have hFG : F = G := by
    apply (cancel_mono hU.isoSpec.hom).mp
    exact Spec.homEquiv.injective he
  rw [← IsOpenImmersion.lift_fac U.ι f (by
    simpa [Set.range_subset_iff] using fun x hx ↦ hfU.ge hx),
    ← IsOpenImmersion.lift_fac U.ι g (by
      simpa [Set.range_subset_iff] using fun x hx ↦ hgU.ge hx)]
  exact congrArg (· ≫ U.ι) hFG

/-- The spectrum of the reconstructed homomorphism commutes with the structure maps. -/
theorem Hom.baseRingHom_over_S {ξ η : FormalObject X} (a : Hom ξ η) :
    Spec.map (CommRingCat.ofHom a.baseRingHom) ≫ η.base.toS = ξ.base.toS := by
  apply hom_ext_of_truncations
  intro n
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    a.baseRingHom_mk n, CommRingCat.ofHom_comp, Spec.map_comp,
    a.quotientHom_spec n, Category.assoc]
  exact Over.w (a.stageOverMap n)

/-- The morphism of complete local algebras determined by a compatible stage family. -/
def Hom.base {ξ η : FormalObject X} (a : Hom ξ η) :
    CompleteLocalSAlgebra.Hom ξ.base η.base where
  hom := a.baseRingHom
  isLocalHom := a.baseRingHom_isLocalHom
  over_S := a.baseRingHom_over_S

/-- Every stage map lifts the corresponding truncation of its reconstructed base map. -/
theorem Hom.over {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    X.p.IsHomLift (a.base.stageMap n) (a.app n) := by
  apply IsHomLift.of_fac X.p _ _ (ξ.over_obj n) (η.over_obj n)
  change a.base.stageMap n = a.stageOverMap n
  apply Over.OverMorphism.ext
  rw [CompleteLocalSAlgebra.Hom.stageMap_left, ← a.quotientHom_spec n]
  congr 1
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext x
  exact RingHom.congr_fun (a.baseRingHom_mk n) x

/-- The base morphism is uniquely characterized by its lifted stage maps. -/
theorem Hom.base_unique {ξ η : FormalObject X} (a : Hom ξ η)
    (b : CompleteLocalSAlgebra.Hom ξ.base η.base)
    (over : ∀ n, X.p.IsHomLift (b.stageMap n) (a.app n)) : a.base = b := by
  have ext_hom (f g : CompleteLocalSAlgebra.Hom ξ.base η.base)
      (h : f.hom = g.hom) : f = g := by
    cases f
    cases g
    cases h
    rfl
  apply ext_hom
  apply RingHom.ext
  intro x
  apply (AdicCompletion.ofAlgEquiv (maximalIdeal ξ.base.carrier)).injective
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [AdicCompletion.ofAlgEquiv_apply, AdicCompletion.evalₐ_of]
  have hstage (k : ℕ) : a.stageOverMap k = b.stageMap k := by
    letI := over k
    exact (IsHomLift.fac X.p (b.stageMap k) (a.app k)).symm
  have hq (k : ℕ) : a.quotientHom k = (b.stageRingHom k).hom := by
    have he : CommRingCat.ofHom (a.quotientHom k) = b.stageRingHom k := by
      apply Spec.map_injective
      rw [a.quotientHom_spec k, hstage k]
      rfl
    exact congrArg CommRingCat.Hom.hom he
  have hm := RingHom.congr_fun (a.baseRingHom_mk n) x
  rw [hq n] at hm
  exact congrArg (Ideal.Quotient.factorPow (maximalIdeal ξ.base.carrier)
    (Nat.le_succ n)) hm

/-- Construct a natural stage family with a specified compatible base morphism. -/
def Hom.of {ξ η : FormalObject X} (app : ∀ n, ξ.objects n ⟶ η.objects n)
    (base : CompleteLocalSAlgebra.Hom ξ.base η.base)
    (over : ∀ n, X.p.IsHomLift (base.stageMap n) (app n))
    (naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n) : Hom ξ η :=
  Hom.ofStages app naturality

/-- The reconstructed base of a family lifting a specified base is that specified base. -/
theorem Hom.of_base {ξ η : FormalObject X} (app : ∀ n, ξ.objects n ⟶ η.objects n)
    (base : CompleteLocalSAlgebra.Hom ξ.base η.base)
    (over : ∀ n, X.p.IsHomLift (base.stageMap n) (app n))
    (naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n) :
    (Hom.of app base over naturality).base = base :=
  Hom.base_unique _ base over

/-- Identity natural transformation of a formal object. -/
def Hom.id (ξ : FormalObject X) : Hom ξ ξ := 𝟙 ξ.toFunctor

/-- Composition of natural stage families. -/
def Hom.comp {ξ η ζ : FormalObject X} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ := a ≫ b

/-- The identity natural transformation has identity stage maps. -/
theorem Hom.id_app (ξ : FormalObject X) (n : ℕ) :
    (Hom.id ξ).app n = 𝟙 (ξ.objects n) := rfl

/-- Reconstruction takes identity stage maps to the identity base morphism. -/
theorem Hom.id_base (ξ : FormalObject X) :
    (Hom.id ξ).base = CompleteLocalSAlgebra.Hom.id ξ.base := by
  apply Hom.base_unique
  intro n
  have h : (CompleteLocalSAlgebra.Hom.id ξ.base).stageMap n =
      𝟙 (ξ.base.stageOver n) := by
    apply Over.OverMorphism.ext
    change Spec.map _ = 𝟙 _
    rw [Spec.map_eq_id]
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    rfl
  rw [h, Hom.id_app]
  exact IsHomLift.id (ξ.over_obj n)

/-- Composition of natural transformations is stagewise composition. -/
theorem Hom.comp_app {ξ η ζ : FormalObject X} (a : Hom ξ η) (b : Hom η ζ) (n : ℕ) :
    (Hom.comp a b).app n = a.app n ≫ b.app n := rfl

/-- Reconstruction commutes with composition of compatible stage families. -/
theorem Hom.comp_base {ξ η ζ : FormalObject X} (a : Hom ξ η) (b : Hom η ζ) :
    (Hom.comp a b).base = CompleteLocalSAlgebra.Hom.comp a.base b.base := by
  apply Hom.base_unique
  intro n
  have h : (CompleteLocalSAlgebra.Hom.comp a.base b.base).stageMap n =
      a.base.stageMap n ≫ b.base.stageMap n := by
    apply Over.OverMorphism.ext
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    rfl
  rw [h, Hom.comp_app]
  letI := a.over n
  letI := b.over n
  infer_instance

/-- Stage maps lift the reconstructed base and commute with successor transitions. -/
theorem Hom.spec {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    X.p.IsHomLift (a.base.stageMap n) (a.app n) ∧
      ξ.step n ≫ a.app (n + 1) = a.app n ≫ η.step n := by
  refine ⟨a.over n, ?_⟩
  have h := a.naturality (homOfLE (Nat.le_add_right n 1))
  dsimp only [toFunctor, Functor.ofSequence] at h
  rw [Functor.OfSequence.map_le_succ, Functor.OfSequence.map_le_succ] at h
  exact h

/-- The spectrum morphism induced by the reconstructed map on complete local rings. -/
def Hom.overMorphism {ξ η : FormalObject X} (a : Hom ξ η) :
    Spec (CommRingCat.of ξ.base.carrier) ⟶ Spec (CommRingCat.of η.base.carrier) :=
  a.base.toSpec

/-- The induced spectrum morphism is the spectrum of the reconstructed base homomorphism. -/
theorem Hom.overMorphism_eq {ξ η : FormalObject X} (a : Hom ξ η) :
    a.overMorphism = a.base.toSpec := rfl

/-- The induced spectrum morphism is a morphism over the base scheme. -/
theorem Hom.liesOver {ξ η : FormalObject X} (a : Hom ξ η) :
    a.overMorphism ≫ η.base.toS = ξ.base.toS := a.base.over_S

end AlgebraicGeometry.GroupoidsOver.FormalObject
