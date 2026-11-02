/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Orbits
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.PowerSeries
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.SmallestDescent.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.QuasiInitial
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion

/-!
# Minimal versal formal objects

A predeformation category with a versal formal object admits a minimal versal
formal object, unique up to isomorphism; every versal object is the pushforward
of a minimal versal formal object along a finite-variable power series extension.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

private theorem injective_of_surjective_ringEndomorphism {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f : R →+* R) (hf : Function.Surjective f) : Function.Injective f := by
  let c : ℕ → Ideal R := fun n ↦ (Ideal.comap f)^[n] ⊥
  have hc : Monotone c := by
    apply monotone_nat_of_le_succ
    intro n
    induction n with
    | zero => exact bot_le
    | succ n ih =>
      simpa only [c, Function.iterate_succ_apply'] using Ideal.comap_mono (f := f) ih
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance ⟨c, hc⟩
  have hn' : (Ideal.comap f)^[n] ⊥ = (Ideal.comap f)^[n + 1] ⊥ :=
    hn (n + 1) (Nat.le_succ n)
  have heq : (⊥ : Ideal R) = Ideal.comap f ⊥ :=
    (Ideal.comap_injective_of_surjective f hf).iterate n
      (by simpa only [Function.iterate_succ_apply] using hn')
  exact (RingHom.injective_iff_ker_eq_bot f).2 heq.symm

private theorem completeLocal_hom_ext {R S : CompleteLocalAlgCat Λ k} {f g : R ⟶ S}
    (h : f.hom = g.hom) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      cases h
      cases hf
      cases hg
      rfl

private theorem completeLocal_isIso_of_bijective {R S : CompleteLocalAlgCat Λ k}
    (f : R ⟶ S) (hf : Function.Bijective f.hom) : IsIso f := by
  let e := AlgEquiv.ofBijective f.hom hf
  letI : IsLocalHom e.symm.toAlgHom :=
    isLocalHom_of_leftInverse e.toAlgHom e.apply_symm_apply
  have hcompat : residueCompat e.symm.toAlgHom inferInstance = residueIsoHom S := by
    ext z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    change R.residueFieldIso
        (IsLocalRing.ResidueField.mapAlgHom e.symm.toAlgHom (IsLocalRing.residue S.carrier x)) =
      S.residueFieldIso (IsLocalRing.residue S.carrier x)
    rw [IsLocalRing.ResidueField.mapAlgHom_residue]
    have hx := DFunLike.congr_fun f.residue_compat
      (IsLocalRing.residue R.carrier (e.symm x))
    change S.residueFieldIso
        (IsLocalRing.ResidueField.mapAlgHom f.hom (IsLocalRing.residue R.carrier (e.symm x))) =
      R.residueFieldIso (IsLocalRing.residue R.carrier (e.symm x)) at hx
    rw [IsLocalRing.ResidueField.mapAlgHom_residue] at hx
    change S.residueFieldIso (IsLocalRing.residue S.carrier (e (e.symm x))) = _ at hx
    rw [e.apply_symm_apply] at hx
    exact hx.symm
  let g : S ⟶ R := CompleteLocalAlgCat.Hom.of e.symm.toAlgHom inferInstance hcompat
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply completeLocal_hom_ext
    exact AlgHom.ext e.symm_apply_apply
  · apply completeLocal_hom_ext
    exact AlgHom.ext e.apply_symm_apply

private theorem isIso_of_isMinimalVersal [Functor.IsPredeformationCategory p]
    {ξ η : FormalObject p} [FormalObject.IsMinimalVersal ξ] [FormalObject.IsMinimalVersal η]
    (f : ξ ⟶ η) : IsIso f := by
  obtain ⟨g⟩ := FormalObject.exists_hom_of_isVersal η ξ
  have hf := FormalObject.IsMinimalVersal.spec η f
  have hg := FormalObject.IsMinimalVersal.spec ξ g
  have hinj := injective_of_surjective_ringEndomorphism (g.base.hom.toRingHom.comp f.base.hom.toRingHom)
    (hg.comp hf)
  have hbij : Function.Bijective f.base.hom := ⟨fun x y hxy ↦ hinj (congrArg g.base.hom hxy), hf⟩
  letI := completeLocal_isIso_of_bijective f.base hbij
  letI : IsIso ((Functor.completion p).op.map f.op) :=
    inferInstanceAs (IsIso f.base.op)
  letI := Functor.IsFibered.InGroupoids.all_isStronglyCartesian
    (p := (Functor.completion p).op) f.op
  letI : IsIso f.op := Functor.IsStronglyCartesian.isIso_of_base_isIso
    ((Functor.completion p).op) ((Functor.completion p).op.map f.op) f.op
  exact isIso_of_op f

/-- A predeformation category with a versal formal object has a minimal versal
formal object. -/
theorem exists_isMinimalVersal [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] :
    ∃ ξ' : FormalObject p, IsMinimalVersal ξ' := by
  letI := Functor.hasSchlessingerS1_of_isVersal p ξ
  obtain ⟨ξ', f, hf⟩ := exists_isSmallestDescent ξ
  exact ⟨ξ', { toIsVersal := hf.isVersal, surjective_base := fun g ↦ hf.2.2 g }⟩

/-- Any two minimal versal formal objects of a predeformation category are isomorphic. -/
theorem nonempty_iso [Functor.IsPredeformationCategory p]
    (ξ η : FormalObject p) [IsMinimalVersal ξ] [IsMinimalVersal η] :
    Nonempty (ξ ≅ η) := by
  obtain ⟨f⟩ := exists_hom_of_isVersal ξ η
  letI := isIso_of_isMinimalVersal f
  exact ⟨asIso f⟩

/-- Every versal formal object of a predeformation category receives a morphism from
a minimal versal formal object whose base map is a finite-variable power series extension. -/
theorem exists_isPowerSeriesOver [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] :
    ∃ (ξ' : FormalObject p) (f : ξ' ⟶ ξ),
      IsMinimalVersal ξ' ∧ IsPowerSeriesOver f.base := by
  letI := Functor.hasSchlessingerS1_of_isVersal p ξ
  obtain ⟨ξ', f, hf⟩ := exists_isSmallestDescent ξ
  exact ⟨ξ', f,
    { toIsVersal := hf.isVersal, surjective_base := fun g ↦ hf.2.2 g },
    hf.isPowerSeriesOver⟩

/-- Every morphism between minimal versal formal objects of a predeformation category
is an isomorphism. -/
instance isIso [Functor.IsPredeformationCategory p]
    {ξ η : FormalObject p} [IsMinimalVersal ξ] [IsMinimalVersal η]
    (f : ξ ⟶ η) : IsIso f :=
  isIso_of_isMinimalVersal f

/-- A versal formal object of a predeformation category whose differential is
bijective on residue-derivation orbits is minimal versal. -/
theorem isMinimalVersal_of_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] (ξ : FormalObject p) [IsVersal ξ]
    (h : BijectiveDifferentialOnOrbits ξ) : IsMinimalVersal ξ := sorry

/-- A versal formal object with Fact-certified orbit bijectivity of its
differential is minimal versal. -/
instance instIsMinimalVersalOfBijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] (ξ : FormalObject p) [IsVersal ξ]
    [Fact (BijectiveDifferentialOnOrbits ξ)] : IsMinimalVersal ξ :=
  isMinimalVersal_of_bijectiveDifferentialOnOrbits ξ Fact.out

/-- Any two versal formal objects of a predeformation category whose differentials
are bijective on residue-derivation orbits are isomorphic. -/
theorem nonempty_iso_of_bijectiveDifferentialOnOrbits
    [Functor.IsPredeformationCategory p] (ξ η : FormalObject p)
    [IsVersal ξ] [IsVersal η] (hξ : BijectiveDifferentialOnOrbits ξ)
    (hη : BijectiveDifferentialOnOrbits η) : Nonempty (ξ ≅ η) := by
  letI := isMinimalVersal_of_bijectiveDifferentialOnOrbits ξ hξ
  letI := isMinimalVersal_of_bijectiveDifferentialOnOrbits η hη
  exact nonempty_iso ξ η

/-- The differential of a minimal versal formal object of a predeformation category
satisfying Schlessinger's condition (S2) is bijective on residue-derivation orbits. -/
theorem bijectiveDifferentialOnOrbits_of_isMinimalVersal
    [Functor.IsPredeformationCategory p] [Functor.HasSchlessingerS2 p]
    (ξ : FormalObject p) [IsMinimalVersal ξ] :
    BijectiveDifferentialOnOrbits ξ := sorry

end FormalObject
