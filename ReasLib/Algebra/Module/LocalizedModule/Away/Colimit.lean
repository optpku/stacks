/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Group.Submonoid.Divisibility
public import ReasLib.Algebra.Module.LocalizedModule.Away.Map

/-!
# Principal Localizations Indexed by Divisibility

This leaf records the diagram of principal localizations indexed by the
divisibility preorder on a submonoid and its canonical cocone into the total
localization.

The descent morphism below is concrete; its well-definedness, linearity, and universal
property follow by transporting fractions to common denominators.

@stack 00CR
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace LocalizedModule.Away

variable {R : Type u} [CommRing R]

private theorem restriction_mk_one
    {M : Type v} [AddCommGroup M] [Module R M]
    (a b : R) (h : a ∣ b) (m : M) :
    mapOfDvd a b h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  simp only [mapOfDvd, mapOfIsUnit, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LocalizedModule.equivTensorProduct_apply_mk, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, LinearMap.id_apply, Localization.mk_one, map_one,
    LocalizedModule.equivTensorProduct_symm_apply_tmul_one]

private theorem smul_mk_pow
    {M : Type v} [AddCommGroup M] [Module R M] (a : R) (n : ℕ) (m : M) :
    a ^ n • LocalizedModule.mk m (Submonoid.pow a n) = LocalizedModule.mk m 1 := by
  rw [LocalizedModule.smul'_mk]
  exact LocalizedModule.mk_cancel (Submonoid.pow a n) m

private theorem restriction_mk_pow
    {M : Type v} [AddCommGroup M] [Module R M]
    (a b : R) {r : R} (hr : b = a * r) (n : ℕ) (m : M) :
    mapOfDvd a b ⟨r, hr⟩ (LocalizedModule.mk m (Submonoid.pow a n)) =
      LocalizedModule.mk (r ^ n • m) (Submonoid.pow b n) := by
  apply IsLocalizedModule.smul_injective
    (LocalizedModule.mkLinearMap (Submonoid.powers b) M) (Submonoid.pow b n)
  change b ^ n • mapOfDvd a b ⟨r, hr⟩ (LocalizedModule.mk m (Submonoid.pow a n)) =
    b ^ n • LocalizedModule.mk (r ^ n • m) (Submonoid.pow b n)
  rw [smul_mk_pow]
  calc
    b ^ n • mapOfDvd a b ⟨r, hr⟩ (LocalizedModule.mk m (Submonoid.pow a n)) =
        mapOfDvd a b ⟨r, hr⟩
          (r ^ n • (a ^ n • LocalizedModule.mk m (Submonoid.pow a n))) := by
      rw [← map_smul]
      apply congrArg (mapOfDvd a b ⟨r, hr⟩)
      rw [hr, mul_pow, mul_smul, smul_comm]
    _ = r ^ n • LocalizedModule.mk m 1 := by
      rw [smul_mk_pow, map_smul, restriction_mk_one]
    _ = LocalizedModule.mk (r ^ n • m) 1 := LocalizedModule.smul'_mk _ _ _

private theorem toTotal_mk_pow
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (s : S) (n : ℕ) (m : M) :
    toLocalizedModule S s (LocalizedModule.mk m (Submonoid.pow (s : R) n)) =
      LocalizedModule.mk m (s ^ n) := by
  rw [IsLocalizedModule.mk_eq_mk']
  rw [toLocalizedModule, IsLocalizedModule.liftOfLE_mk']
  rw [IsLocalizedModule.mk_eq_mk']
  apply congrArg (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) m)
  apply Subtype.ext
  rfl

/-- Tag `00CR`: the `ModuleCat R` morphism between principal localizations
induced by a divisibility relation inside a submonoid. -/
@[stacks 00CR "principal localized module divisibility morphism"]
noncomputable def divisibilityMap
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    {a b : S.Divisibility} (h : a ≤ b) :
    ModuleCat.of R (LocalizedModule.Away (a : R) M) ⟶
      ModuleCat.of R (LocalizedModule.Away (b : R) M) :=
  ModuleCat.ofHom (mapOfDvd (M := M) (a : R) (b : R) h)

/-- The divisibility morphism at an identity relation is the identity module
morphism. -/
@[simp, stacks 00CR "principal localized module divisibility identity"]
theorem divisibilityMap_id
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (s : S.Divisibility) :
    divisibilityMap S M (leOfHom (𝟙 s)) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m t =>
    obtain ⟨_, ⟨n, rfl⟩⟩ := t
    have hs : (s : R) ∣ (s : R) := dvd_refl _
    change mapOfDvd (s : R) (s : R) hs
      (LocalizedModule.mk m (Submonoid.pow (s : R) n)) =
        LocalizedModule.mk m (Submonoid.pow (s : R) n)
    simpa only [one_pow, one_smul] using
      (restriction_mk_pow (s : R) (s : R) (mul_one _).symm n m)

/-- Divisibility morphisms between principal localizations compose along
composition in the divisibility preorder. -/
@[stacks 00CR "principal localized module divisibility composition"]
theorem divisibilityMap_comp
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    {a b c : S.Divisibility} (f : a ⟶ b) (g : b ⟶ c) :
    divisibilityMap S M (leOfHom (f ≫ g)) =
      divisibilityMap S M (leOfHom f) ≫ divisibilityMap S M (leOfHom g) := by
  obtain ⟨r, hr⟩ := leOfHom f
  obtain ⟨q, hq⟩ := leOfHom g
  have hc : (c : R) = (a : R) * (r * q) := by
    rw [hq, hr, mul_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m t =>
    obtain ⟨_, ⟨n, rfl⟩⟩ := t
    have hab : (a : R) ∣ (b : R) := ⟨r, hr⟩
    have hbc : (b : R) ∣ (c : R) := ⟨q, hq⟩
    have hac : (a : R) ∣ (c : R) := ⟨r * q, hc⟩
    change mapOfDvd (a : R) (c : R) hac
      (LocalizedModule.mk m (Submonoid.pow (a : R) n)) =
        mapOfDvd (b : R) (c : R) hbc
          (mapOfDvd (a : R) (b : R) hab
            (LocalizedModule.mk m (Submonoid.pow (a : R) n)))
    rw [restriction_mk_pow _ _ hc, restriction_mk_pow _ _ hr,
      restriction_mk_pow _ _ hq]
    simp only [mul_pow, mul_smul, smul_comm (r ^ n) (q ^ n)]

/-- Tag `00CR`: the diagram of principal localizations of `M` indexed by
elements of `S` ordered by divisibility. -/
@[stacks 00CR "principal localized module divisibility diagram"]
noncomputable def divisibilityDiagram
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    S.Divisibility ⥤ ModuleCat R where
  obj s := ModuleCat.of R (LocalizedModule.Away (s : R) M)
  map f := divisibilityMap S M (leOfHom f)
  map_id := fun s ↦ divisibilityMap_id S M s
  map_comp := fun f g ↦ divisibilityMap_comp S M f g

/-- Canonical maps from principal localizations to the total localization are
natural along a divisibility morphism. -/
@[stacks 00CR "principal localized module divisibility cocone naturality"]
theorem divisibilityCocone_naturality
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    {a b : S.Divisibility} (f : a ⟶ b) :
    divisibilityMap S M (leOfHom f) ≫
        ModuleCat.ofHom (toLocalizedModule (M := M) S (b : S)) =
      ModuleCat.ofHom (toLocalizedModule (M := M) S (a : S)) := by
  obtain ⟨r, hr⟩ := leOfHom f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m t =>
    obtain ⟨_, ⟨n, rfl⟩⟩ := t
    have hab : (a : R) ∣ (b : R) := ⟨r, hr⟩
    change toLocalizedModule S (b : S)
      (mapOfDvd (a : R) (b : R) hab
        (LocalizedModule.mk m (Submonoid.pow (a : R) n))) =
          toLocalizedModule S (a : S)
            (LocalizedModule.mk m (Submonoid.pow (a : R) n))
    rw [restriction_mk_pow _ _ hr, toTotal_mk_pow, toTotal_mk_pow]
    apply LocalizedModule.mk_eq.mpr
    refine ⟨1, ?_⟩
    simp only [one_smul]
    calc
      (a : R) ^ n • r ^ n • m = ((a : R) ^ n * r ^ n) • m :=
        (mul_smul _ _ _).symm
      _ = ((a : R) * r) ^ n • m := by rw [mul_pow]
      _ = (b : R) ^ n • m := by rw [hr]

/-- Tag `00CR`: the canonical cocone from the divisibility diagram of
principal localizations to the total localization at `S`. -/
@[stacks 00CR "principal localized module divisibility cocone"]
noncomputable def divisibilityCocone
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    Cocone (divisibilityDiagram S M) where
  pt := ModuleCat.of R (LocalizedModule S M)
  ι :=
    { app := fun s ↦ ModuleCat.ofHom (toLocalizedModule (M := M) S (s : S))
      naturality := fun _ _ f ↦ divisibilityCocone_naturality S M f }

namespace divisibilityCoconeDesc

private theorem cocone_mk_pow
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (s t : S) {r : R}
    (hr : (t : R) = (s : R) * r) (n : ℕ) (m : M) :
    c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) n)) =
      c.ι.app t (LocalizedModule.mk (r ^ n • m) (Submonoid.pow (t : R) n)) := by
  have h := congrArg
    (fun k : ModuleCat.of R (LocalizedModule.Away (s : R) M) ⟶ c.pt ↦
      k (LocalizedModule.mk m (Submonoid.pow (s : R) n)))
    (c.w (homOfLE (show (s : S.Divisibility) ≤ (t : S.Divisibility) from ⟨r, hr⟩)))
  have hst : (s : R) ∣ (t : R) := ⟨r, hr⟩
  change c.ι.app t
    (mapOfDvd (s : R) (t : R) hst
      (LocalizedModule.mk m (Submonoid.pow (s : R) n))) =
        c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) n)) at h
  rw [restriction_mk_pow _ _ hr] at h
  exact h.symm

/-- Evaluating a cocone in the denominator component respects the equivalence relation defining
the total localized module. -/
@[stacks 00CR "principal localization cocone descent well-definedness"]
theorem wellDefined
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (p p' : M × S) (h : p ≈ p') :
    c.ι.app p.2 (LocalizedModule.mk p.1 (Submonoid.pow (p.2 : R) 1)) =
      c.ι.app p'.2 (LocalizedModule.mk p'.1 (Submonoid.pow (p'.2 : R) 1)) := by
  rcases p with ⟨m, s⟩
  rcases p' with ⟨m', t⟩
  obtain ⟨u, hu⟩ := h
  let q : S := u * s * t
  have hs : (q : R) = (s : R) * ((u : R) * (t : R)) := by
    dsimp only [q, Submonoid.coe_mul]
    ac_rfl
  have ht : (q : R) = (t : R) * ((u : R) * (s : R)) := by
    dsimp only [q, Submonoid.coe_mul]
    ac_rfl
  change c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) =
    c.ι.app t (LocalizedModule.mk m' (Submonoid.pow (t : R) 1))
  rw [cocone_mk_pow S M c s q hs, cocone_mk_pow S M c t q ht]
  apply congrArg (fun m : M ↦ c.ι.app q
    (LocalizedModule.mk m (Submonoid.pow (q : R) 1)))
  simpa only [pow_one, mul_smul, Submonoid.smul_def] using hu

/-- The underlying function of the canonical descent morphism evaluates a fraction in the cocone
component indexed by its denominator. -/
@[stacks 00CR "principal localization cocone descent function"]
noncomputable def toFun
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) : LocalizedModule S M → c.pt :=
  fun x ↦ x.liftOn
    (fun p ↦ c.ι.app p.2 (LocalizedModule.mk p.1 (Submonoid.pow (p.2 : R) 1)))
    (wellDefined S M c)

/-- The underlying descent function preserves addition. -/
@[stacks 00CR "principal localization cocone descent additivity"]
theorem map_add
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (x y : LocalizedModule S M) :
    toFun S M c (x + y) = toFun S M c x + toFun S M c y := by
  induction x, y using LocalizedModule.induction_on₂ with
  | h m m' s t =>
    rw [LocalizedModule.mk_add_mk]
    simp only [toFun, LocalizedModule.liftOn_mk, Submonoid.smul_def]
    rw [cocone_mk_pow S M c s (s * t) rfl,
      cocone_mk_pow S M c t (s * t) (mul_comm (s : R) (t : R))]
    simp only [pow_one]
    let st : S.Divisibility := (s * t : S)
    let u : Submonoid.powers (st : R) := Submonoid.pow (st : R) 1
    have heq :
        LocalizedModule.mk ((t : R) • m + (s : R) • m') u =
          LocalizedModule.mk ((t : R) • m) u +
            LocalizedModule.mk ((s : R) • m') u := by
      rw [LocalizedModule.mk_add_mk]
      apply LocalizedModule.mk_eq.mpr
      refine ⟨1, ?_⟩
      simp only [one_smul, mul_smul, smul_add]
    change c.ι.app st (LocalizedModule.mk ((t : R) • m + (s : R) • m') u) =
      c.ι.app st (LocalizedModule.mk ((t : R) • m) u) +
        c.ι.app st (LocalizedModule.mk ((s : R) • m') u)
    rw [heq]
    exact (c.ι.app st).hom.map_add _ _

/-- The underlying descent function preserves scalar multiplication. -/
@[stacks 00CR "principal localization cocone descent scalar action"]
theorem map_smul
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (r : R) (x : LocalizedModule S M) :
    toFun S M c (r • x) = r • toFun S M c x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.smul'_mk]
    simp only [toFun, LocalizedModule.liftOn_mk]
    rw [← LocalizedModule.smul'_mk]
    exact (c.ι.app s).hom.map_smul r _

end divisibilityCoconeDesc

/-- The canonical descent morphism from the total localization to the vertex of a cocone on the
principal-localization diagram. -/
@[stacks 00CR "principal localization cocone descent"]
noncomputable def divisibilityCoconeDesc
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) :
    (divisibilityCocone S M).pt ⟶ c.pt :=
  ModuleCat.ofHom
    { toFun := divisibilityCoconeDesc.toFun S M c
      map_add' := divisibilityCoconeDesc.map_add S M c
      map_smul' := divisibilityCoconeDesc.map_smul S M c }

/-- The canonical descent morphism evaluates a localized fraction in the component indexed by its
denominator. -/
@[simp, stacks 00CR "principal localization cocone descent application"]
theorem divisibilityCoconeDesc_apply_mk
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (m : M) (s : S) :
    divisibilityCoconeDesc S M c (LocalizedModule.mk m s) =
      c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) := by
  change divisibilityCoconeDesc.toFun S M c (LocalizedModule.mk m s) = _
  exact LocalizedModule.liftOn_mk _ m s

/-- The canonical descent morphism factors every leg of the total-localization cocone. -/
@[reassoc, simp, stacks 00CR "principal localization cocone descent factorization"]
theorem divisibilityCoconeDesc_fac
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (s : S.Divisibility) :
    (divisibilityCocone S M).ι.app s ≫ divisibilityCoconeDesc S M c = c.ι.app s := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m t =>
    obtain ⟨_, ⟨n, rfl⟩⟩ := t
    change divisibilityCoconeDesc S M c
      (toLocalizedModule S (s : S)
        (LocalizedModule.mk m (Submonoid.pow (s : R) n))) =
          c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) n))
    rw [toTotal_mk_pow, divisibilityCoconeDesc_apply_mk]
    let q : S := (s : S) ^ n
    let b : S.Divisibility := (s : S) * q
    have hq : (b : R) = (q : R) * (s : R) := by
      change (s : R) * (q : R) = (q : R) * (s : R)
      exact mul_comm _ _
    have hs : (b : R) = (s : R) * (q : R) := rfl
    have heq :
        LocalizedModule.mk ((s : R) • m) (Submonoid.pow (b : R) 1) =
          LocalizedModule.mk ((q : R) ^ n • m) (Submonoid.pow (b : R) n) := by
      apply LocalizedModule.mk_eq.mpr
      refine ⟨1, ?_⟩
      change (1 : R) • ((b : R) ^ n • ((s : R) • m)) =
        (1 : R) • ((b : R) ^ 1 • ((q : R) ^ n • m))
      simp only [pow_one, ← mul_smul, one_mul]
      congr 1
      change ((s : R) * (s : R) ^ n) ^ n * (s : R) =
        ((s : R) * (s : R) ^ n) * ((s : R) ^ n) ^ n
      rw [mul_pow]
      ac_rfl
    change c.ι.app q (LocalizedModule.mk m (Submonoid.pow (q : R) 1)) =
      c.ι.app (s : S) (LocalizedModule.mk m (Submonoid.pow (s : R) n))
    rw [divisibilityCoconeDesc.cocone_mk_pow S M c q (b : S) hq,
      divisibilityCoconeDesc.cocone_mk_pow S M c (s : S) (b : S) hs]
    change (c.ι.app b).hom
        (LocalizedModule.mk ((s : R) ^ 1 • m) (Submonoid.pow (b : R) 1)) =
      (c.ι.app b).hom
        (LocalizedModule.mk ((q : R) ^ n • m) (Submonoid.pow (b : R) n))
    rw [pow_one]
    exact congrArg (c.ι.app b).hom heq

/-- A morphism compatible with all principal-localization cocone legs is the canonical descent
morphism. -/
@[stacks 00CR "principal localization cocone descent uniqueness"]
theorem divisibilityCoconeDesc_unique
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M))
    (t : (divisibilityCocone S M).pt ⟶ c.pt)
    (ht : ∀ s : S.Divisibility, (divisibilityCocone S M).ι.app s ≫ t = c.ι.app s) :
    t = divisibilityCoconeDesc S M c := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [divisibilityCoconeDesc_apply_mk]
    have h := congrArg
      (fun k : ModuleCat.of R (LocalizedModule.Away (s : R) M) ⟶ c.pt ↦
        k (LocalizedModule.mk m (Submonoid.pow (s : R) 1))) (ht s)
    change t (toLocalizedModule S s
      (LocalizedModule.mk m (Submonoid.pow (s : R) 1))) =
        c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) at h
    rw [toTotal_mk_pow, pow_one] at h
    exact h

/-- Tag `00CR`: every cocone on principal localizations indexed by
divisibility admits a unique compatible morphism from the total localization.
This is the universal-property form suitable for the statement stage. -/
@[stacks 00CR "principal localized module divisibility universal property"]
theorem divisibilityCocone_existsUniqueDesc
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) :
    ∃! t : (divisibilityCocone S M).pt ⟶ c.pt,
      ∀ s : S.Divisibility, (divisibilityCocone S M).ι.app s ≫ t = c.ι.app s := by
  exact ⟨divisibilityCoconeDesc S M c, divisibilityCoconeDesc_fac S M c,
    fun t ht ↦ divisibilityCoconeDesc_unique S M c t ht⟩

/-- Lemma 10.9.9: the total localization is the colimit of the principal-localization diagram.

The `IsColimit` owner is kept beside the diagram and cocone so downstream users can consume one
canonical object instead of rebuilding a source-specific descent proof. -/
@[stacks 00CR "principal localization colimit"]
noncomputable def divisibilityCocone_isColimit
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsColimit (divisibilityCocone S M) where
  desc := divisibilityCoconeDesc S M
  fac := divisibilityCoconeDesc_fac S M
  uniq := divisibilityCoconeDesc_unique S M

/-- The colimit comparison map restricts to each cocone leg. -/
@[reassoc, simp, stacks 00CR "principal localization colimit factorization"]
theorem divisibilityCocone_isColimit_fac
    (S : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M]
    (c : Cocone (divisibilityDiagram S M)) (s : S.Divisibility) :
    (divisibilityCocone S M).ι.app s ≫
        (divisibilityCocone_isColimit S M).desc c = c.ι.app s := by
  exact (divisibilityCocone_isColimit S M).fac c s

end LocalizedModule.Away
