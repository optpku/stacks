module

public import stacks_project.Chap10.Lemma_10_24_5.GlueingComparisons
import StacksCheckRecall

/-!
# Lemma 10.24.5

The source-facing normal forms for the left and right target branches and their
triple-overlap transports are recorded here over the concrete localized-module
data supplied by `GlueingComparisons`.

@stack 00EQ
-/

@[expose] public section

open CategoryTheory LinearMap LocalizedModule IsLocalizedModule

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

-- Local declaration justification (source-local notation): `Away` abbreviates
-- the repeated `LocalizedModule.Away` carrier in the source-facing formulas;
-- no local instance or semantic choice is hidden by this notation.
local notation "Away" => LocalizedModule.Away

namespace AwayModuleGlueing

variable {f : Fin n → R} (glue : AwayModuleGlueing f)

-- The unit witness passed to `LocalizedModule.lift` is proof-only; the localization map remains
-- explicit concrete data, while the source compatibility criterion is owned upstream.
/-- Helper for Lemma 10.24.5: the standard `(j,k)` target differential lifts the `j`-branch from
the `j`-th localization of the distinguished `i`-piece to the common `(j,k)` overlap. -/
noncomputable abbrev standard_target_left_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f j) (glue.localModule i) →ₗ[R] Away (f j * f k) (glue.localModule i) :=
  LocalizedModule.lift (.powers (f j))
    (LocalizedModule.mkLinearMap (.powers (f j * f k)) (glue.localModule i))
    (fun x ↦ by
      rcases (Submonoid.mem_powers_iff x.1 (f j)).mp x.2 with ⟨n, hn⟩
      have hfj :
          IsUnit (algebraMap R (Module.End R (Away (f j * f k) (glue.localModule i))) (f j)) :=
        away_module_end_isUnit_of_dvd (glue.localModule i) (f j * f k) (f j) (dvd_mul_right _ _)
      simpa [map_pow, ← hn] using hfj.pow n)

/-- Helper for Lemma 10.24.5: the standard `(j,k)` target differential lifts the `k`-branch from
the `k`-th localization of the distinguished `i`-piece to the common `(j,k)` overlap. -/
noncomputable abbrev standard_target_right_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f k) (glue.localModule i) →ₗ[R] Away (f j * f k) (glue.localModule i) :=
  LocalizedModule.lift (.powers (f k))
    (LocalizedModule.mkLinearMap (.powers (f j * f k)) (glue.localModule i))
    (fun x ↦ by
      rcases (Submonoid.mem_powers_iff x.1 (f k)).mp x.2 with ⟨n, hn⟩
      have hfk :
          IsUnit (algebraMap R (Module.End R (Away (f j * f k) (glue.localModule i))) (f k)) :=
        away_module_end_isUnit_of_dvd (glue.localModule i) (f j * f k) (f k) (dvd_mul_left _ _)
      simpa [map_pow, ← hn] using hfk.pow n)

/-- Helper for Lemma 10.24.5: powers of `f j` act invertibly on the standard left target
localization. -/
theorem standard_target_left_lift_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f j),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (glue.localModule i))) x) := sorry

/-- Helper for Lemma 10.24.5: the standard left branch lift sends a canonical generator to the
same canonical generator in the overlap localization. -/
theorem standard_target_left_lift_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule i) :
    glue.standard_target_left_lift i j k (LocalizedModule.mk x 1) =
      (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule i)) := sorry

/-- Helper for Lemma 10.24.5: every power of `f j` acts invertibly on the nested left target
localization used before collapsing the trivial `f i`-factor. -/
theorem standard_target_left_inner_lift_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f j),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (Away (f i) (glue.localModule i)))) x) := sorry

/-- Helper for Lemma 10.24.5: before collapsing the trivial `f i`-localization, the standard left
branch lift is just the usual localization lift on `Away (f i) (glue.localModule i)`. -/
noncomputable abbrev standard_target_left_inner_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f j) (Away (f i) (glue.localModule i)) →ₗ[R]
      Away (f j * f k) (Away (f i) (glue.localModule i)) :=
  LocalizedModule.lift (.powers (f j))
    (LocalizedModule.mkLinearMap (.powers (f j * f k)) (Away (f i) (glue.localModule i)))
    (glue.standard_target_left_inner_lift_powers_isUnit i j k)

/-- Helper for Lemma 10.24.5: the inner left lift sends a canonical generator to the same
canonical generator in the overlap localization. -/
theorem standard_target_left_inner_lift_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : Away (f i) (glue.localModule i)) :
    glue.standard_target_left_inner_lift i j k (LocalizedModule.mk x 1) =
      (LocalizedModule.mk x 1 : Away (f j * f k) (Away (f i) (glue.localModule i))) := sorry

/-- Helper for Lemma 10.24.5: collapsing the trivial `f i`-localization commutes with the
standard left branch lift after transporting the source along the same collapse equivalence. -/
theorem standard_target_left_lift_collapse_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : Away (f i) (glue.localModule i)) :
    (((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
        ((glue.standard_target_left_lift i j k).comp
          (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i)).toLinearMap))
      (LocalizedModule.mk x 1) =
        glue.standard_target_left_inner_lift i j k (LocalizedModule.mk x 1) := sorry

/-- Helper for Lemma 10.24.5: collapsing the trivial `f i`-localization commutes with the
standard left branch lift after precomposing with the canonical generator map. -/
theorem standard_target_left_lift_collapse_natural
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    (((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
        ((glue.standard_target_left_lift i j k).comp
          (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i)).toLinearMap)).comp
      (LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i))) =
    (glue.standard_target_left_inner_lift i j k).comp
      (LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i))) := sorry

/-- Helper for Lemma 10.24.5: after stripping the outer collapse equivalence, the standard left
branch lift agrees with the inner localization lift. -/
theorem standard_target_left_lift_overlap_inner_normal_form
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (z : Away (f j) (Away (f i) (glue.localModule i))) :
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
      (glue.standard_target_left_lift i j k
        (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i) z)) =
      glue.standard_target_left_inner_lift i j k z := sorry

/-- Helper for Lemma 10.24.5: the standard right branch lift sends a canonical generator to the
same canonical generator in the overlap localization. -/
theorem standard_target_right_lift_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f k),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (glue.localModule i))) x) := sorry

/-- Helper for Lemma 10.24.5: the standard right branch lift sends a canonical generator to the
same canonical generator in the overlap localization. -/
theorem standard_target_right_lift_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule i) :
    glue.standard_target_right_lift i j k (LocalizedModule.mk x 1) =
      (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule i)) := sorry

/-- Helper for Lemma 10.24.5: every power of `f k` acts invertibly on the nested right target
localization used before collapsing the trivial `f i`-factor. -/
theorem standard_target_right_inner_lift_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f k),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (Away (f i) (glue.localModule i)))) x) := sorry

/-- Helper for Lemma 10.24.5: before collapsing the trivial `f i`-localization, the standard right
branch lift is just the usual localization lift on `Away (f i) (glue.localModule i)`. -/
noncomputable abbrev standard_target_right_inner_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f k) (Away (f i) (glue.localModule i)) →ₗ[R]
      Away (f j * f k) (Away (f i) (glue.localModule i)) :=
  LocalizedModule.lift (.powers (f k))
    (LocalizedModule.mkLinearMap (.powers (f j * f k)) (Away (f i) (glue.localModule i)))
    (glue.standard_target_right_inner_lift_powers_isUnit i j k)

/-- Helper for Lemma 10.24.5: the inner right lift sends a canonical generator to the same
canonical generator in the overlap localization. -/
theorem standard_target_right_inner_lift_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : Away (f i) (glue.localModule i)) :
    glue.standard_target_right_inner_lift i j k (LocalizedModule.mk x 1) =
      (LocalizedModule.mk x 1 : Away (f j * f k) (Away (f i) (glue.localModule i))) := sorry

/-- Helper for Lemma 10.24.5: collapsing the trivial `f i`-localization commutes with the
standard right branch lift after transporting the source along the same collapse equivalence. -/
theorem standard_target_right_lift_collapse_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : Away (f i) (glue.localModule i)) :
    (((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
        ((glue.standard_target_right_lift i j k).comp
          (awayLocalizeLinearEquiv (f k) (glue.localModuleAwayEquiv i)).toLinearMap))
      (LocalizedModule.mk x 1) =
        glue.standard_target_right_inner_lift i j k (LocalizedModule.mk x 1) := sorry

/-- Helper for Lemma 10.24.5: collapsing the trivial `f i`-localization commutes with the
standard right branch lift after precomposing with the canonical generator map. -/
theorem standard_target_right_lift_collapse_natural
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    (((awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm.toLinearMap).comp
        ((glue.standard_target_right_lift i j k).comp
          (awayLocalizeLinearEquiv (f k) (glue.localModuleAwayEquiv i)).toLinearMap)).comp
      (LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i))) =
    (glue.standard_target_right_inner_lift i j k).comp
      (LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i))) := sorry

/-- Helper for Lemma 10.24.5: after stripping the outer collapse equivalence, the standard right
branch lift agrees with the inner localization lift. -/
theorem standard_target_right_lift_overlap_inner_normal_form
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (z : Away (f k) (Away (f i) (glue.localModule i))) :
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
      (glue.standard_target_right_lift i j k
        (awayLocalizeLinearEquiv (f k) (glue.localModuleAwayEquiv i) z)) =
      glue.standard_target_right_inner_lift i j k z := sorry

/-- Helper for Lemma 10.24.5: the inverse `(1,2)` triple-overlap transport sends a canonical
generator on the `j`-piece to the canonical overlap-transported generator on the `i`-piece. -/
theorem triple_overlap_hom12_symm_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule j) :
    ((awayModuleGlueingTripleOverlapHom12 f glue.localModule glue.overlapIso i j k).symm)
        (LocalizedModule.mk x 1) =
      (awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i))
        (LocalizedModule.mk
          ((((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1 : Away (f i * f j) (glue.localModule j)))) 1) := sorry

/-- Helper for Lemma 10.24.5: the inverse `(1,3)` triple-overlap transport sends a canonical
generator on the `k`-piece to the canonical overlap-transported generator on the `i`-piece. -/
theorem triple_overlap_hom13_symm_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    ((awayModuleGlueingTripleOverlapHom13 f glue.localModule glue.overlapIso i j k).symm)
        (LocalizedModule.mk x 1) =
      (awayEqLinearEquiv (glue.localModule i) (mul_right_comm (f i) (f j) (f k))).symm
        ((awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i))
          (LocalizedModule.mk
            ((((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
              (LocalizedModule.mk x 1 : Away (f i * f k) (glue.localModule k)))) 1)) := sorry

/-- Helper for Lemma 10.24.5: the inverse of the `(2,3)` triple-overlap transport is the
explicit composite of the inverses of its three defining factors. -/
theorem triple_overlap_hom23_symm_apply
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : Away (f i * f j * f k) (glue.localModule k)) :
    ((awayModuleGlueingTripleOverlapHom23 f glue.localModule glue.overlapIso i j k).symm) x =
      let left :
          Away (f i * f j * f k) (glue.localModule j) ≃ₗ[R]
            Away (f j * f k * f i) (glue.localModule j) :=
        awayEqLinearEquiv (glue.localModule j) (mul_rotate (f i) (f j) (f k))
      let center :
          Away (f j * f k * f i) (glue.localModule j) ≃ₗ[R]
            Away (f j * f k * f i) (glue.localModule k) :=
        (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j)).symm.trans
          ((awayLocalizeLinearEquiv (f i) ((glue.overlapIso j k).toLinearEquiv.restrictScalars R)).trans
            (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule k)))
      let right :
          Away (f j * f k * f i) (glue.localModule k) ≃ₗ[R]
            Away (f i * f j * f k) (glue.localModule k) :=
        awayEqLinearEquiv (glue.localModule k) (mul_rotate (f i) (f j) (f k)).symm
      left.symm (center.symm (right.symm x)) := sorry

/-- Helper for Lemma 10.24.5: the inverse of the middle factor in the `(2,3)` triple-overlap
transport sends a canonical generator to the canonical overlap-transported generator. -/
theorem triple_overlap_hom23_center_symm_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    let center :
        Away (f j * f k * f i) (glue.localModule j) ≃ₗ[R]
          Away (f j * f k * f i) (glue.localModule k) :=
      (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j)).symm.trans
        ((awayLocalizeLinearEquiv (f i) ((glue.overlapIso j k).toLinearEquiv.restrictScalars R)).trans
          (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule k)))
    center.symm (LocalizedModule.mk x 1) =
      (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j))
        (LocalizedModule.mk
          ((((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule k)))) 1) := sorry

/-- Helper for Lemma 10.24.5: the outer inverse equality transport in the `(2,3)` triple-overlap
comparison is exactly the domain-reordering transport used in the localized target component. -/
theorem triple_overlap_hom23_outer_symm_eq_domain_transport
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
  let left :
      Away (f i * f j * f k) (glue.localModule j) ≃ₗ[R]
        Away (f j * f k * f i) (glue.localModule j) :=
      awayEqLinearEquiv (glue.localModule j) (mul_rotate (f i) (f j) (f k))
  left.symm =
      awayEqLinearEquiv (glue.localModule j)
        (AwayModuleGlueing.localized_target_component_domain_eq (f := f) i j k) := sorry

/-- Helper for Lemma 10.24.5: the first two steps of the right target-component transport rewrite
the canonical `k`-branch generator into the common triple-overlap model. -/
theorem localized_target_component_transport_overlap_right_generator
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    (awayEqLinearEquiv (glue.localModule j)
        (AwayModuleGlueing.localized_target_component_domain_eq (f := f) i j k))
      ((awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j))
        (LocalizedModule.mk
          ((((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1 :
              Away (f j * f k) (glue.localModule k)))) 1)) =
      ((awayModuleGlueingTripleOverlapHom23 f glue.localModule glue.overlapIso i j k).symm)
        (LocalizedModule.mk x 1) := sorry

/-- Helper for Lemma 10.24.5: powers of the distinguished element `f i` remain invertible after
passing to the target-side overlap localization built on `Away (f i) (glue.localModule i)`. -/
theorem double_away_target_powers_isUnit
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    ∀ x : Submonoid.powers (f i),
      IsUnit
        (algebraMap R
          (Module.End R (Away (f j * f k) (Away (f i) (glue.localModule i)))) x) := sorry

/-- Helper for Lemma 10.24.5: the left branch of the localized target comparison matches the
standard `j`-branch lift in the unit-case Cech differential. -/
noncomputable abbrev stripped_left_transport
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f j) (Away (f i) (glue.localModule i)) →ₗ[R]
      Away (f j * f k) (Away (f i) (glue.localModule i)) :=
  ((awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm.toLinearMap).comp
    (((awayEqLinearEquiv (glue.localModule i)
        (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k)).toLinearMap).comp
      (((awayMulLinearEquiv (f i * f j) (f k) (glue.localModule i)).toLinearMap).comp
        ((LocalizedModule.mkLinearMap (.powers (f k))
          (Away (f i * f j) (glue.localModule i))).comp
          (awayMulLinearEquiv (f i) (f j) (glue.localModule i)).toLinearMap)))

/-- Helper for Lemma 10.24.5: once the left branch is rewritten into the common iterated
localization model, the remaining transport is the canonical inner left lift. -/
theorem stripped_left_transport_eq_standard_target_left_inner_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    (glue.stripped_left_transport i j k).comp
        (LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i))) =
      (glue.standard_target_left_inner_lift i j k).comp
        (LocalizedModule.mkLinearMap (.powers (f j)) (Away (f i) (glue.localModule i))) := sorry

/-- Helper for Lemma 10.24.5: the stripped left transport equals the standard inner left lift as a
map out of the `j`-localization of the distinguished `i`-piece. -/
theorem stripped_left_transport_eq_standard_target_left_inner
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    glue.stripped_left_transport i j k = glue.standard_target_left_inner_lift i j k := sorry

/-- Helper for Lemma 10.24.5: the left branch proof should compare the stripped transport with the
standard inner left lift as a map, not by adding more pointwise generator lemmas. -/
theorem localized_target_component_left_branch_normal_form
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule j) :
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
      (glue.localized_target_component_equiv i j k
        (LocalizedModule.mk
          (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule j)) 1)) =
      glue.stripped_left_transport i j k
        ((awayMulLinearEquiv (f i) (f j) (glue.localModule i)).symm
          (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1))) := sorry

/-- Helper for Lemma 10.24.5: the left target branch is the standard `j`-branch lift after the
outer collapse transport is normalized. -/
theorem localized_target_component_equiv_apply_left_branch_generator
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule j) :
    glue.localized_target_component_equiv i j k
      (LocalizedModule.mk
        (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule j)) 1) =
      glue.standard_target_left_lift i j k
        (glue.local_piece_overlap_equiv i j (LocalizedModule.mk x 1)) := sorry

/-- Helper for Lemma 10.24.5: the right branch of the localized target comparison matches the
standard `k`-branch lift in the unit-case Cech differential. -/
noncomputable abbrev stripped_right_transport
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f k) (Away (f i) (glue.localModule i)) →ₗ[R]
      Away (f j * f k) (Away (f i) (glue.localModule i)) :=
  ((awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm.toLinearMap).comp
    (((awayEqLinearEquiv (glue.localModule i)
        (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k)).toLinearMap).comp
      (((awayEqLinearEquiv (glue.localModule i)
          (mul_right_comm (f i) (f j) (f k) : f i * f j * f k = f i * f k * f j)).symm.toLinearMap).comp
        (((awayMulLinearEquiv (f i * f k) (f j) (glue.localModule i)).toLinearMap).comp
          ((LocalizedModule.mkLinearMap (.powers (f j))
            (Away (f i * f k) (glue.localModule i))).comp
            (awayMulLinearEquiv (f i) (f k) (glue.localModule i)).toLinearMap))))

/-- Helper for Lemma 10.24.5: once the right branch is rewritten into the common iterated
localization model, the remaining transport is the canonical inner right lift. -/
theorem stripped_right_transport_eq_standard_target_right_inner_lift
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    (glue.stripped_right_transport i j k).comp
        (LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i))) =
      (glue.standard_target_right_inner_lift i j k).comp
        (LocalizedModule.mkLinearMap (.powers (f k)) (Away (f i) (glue.localModule i))) := sorry

/-- Helper for Lemma 10.24.5: the stripped right transport equals the standard inner right lift as
a map out of the `k`-localization of the distinguished `i`-piece. -/
theorem stripped_right_transport_eq_standard_target_right_inner
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    glue.stripped_right_transport i j k = glue.standard_target_right_inner_lift i j k := sorry

/-- Helper for Lemma 10.24.5: the right branch proof should compare the stripped transport with
the standard inner right lift as a map, after one cocycle replacement. -/
theorem localized_target_component_right_branch_normal_form
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i)).symm
      (glue.localized_target_component_equiv i j k
        (LocalizedModule.mk
          ((((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule k)))) 1)) =
      glue.stripped_right_transport i j k
        ((awayMulLinearEquiv (f i) (f k) (glue.localModule i)).symm
          (((glue.overlapIso i k).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1))) := sorry

/-- Helper for Lemma 10.24.5: the right target branch is the standard `k`-branch lift after the
outer collapse transport is normalized. -/
theorem localized_target_component_equiv_apply_right_branch_generator
    (glue : AwayModuleGlueing f) (i j k : Fin n) (x : glue.localModule k) :
    glue.localized_target_component_equiv i j k
      (LocalizedModule.mk
        ((((glue.overlapIso j k).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mk x 1 : Away (f j * f k) (glue.localModule k)))) 1) =
      glue.standard_target_right_lift i j k
    (glue.local_piece_overlap_equiv i k (LocalizedModule.mk x 1)) := sorry

/- Lemma 10.24.5: the branch and triple-overlap normal forms above are the
source-facing generator and transport clauses for the localized target. -/
@[stacks 00EQ "left branch unit and generator normal forms"]
#check @AwayModuleGlueing.standard_target_left_lift_powers_isUnit
@[stacks 00EQ "left branch generator normal form"]
#check @AwayModuleGlueing.standard_target_left_lift_apply_mk_one
@[stacks 00EQ "right branch unit and generator normal forms"]
#check @AwayModuleGlueing.standard_target_right_lift_powers_isUnit
@[stacks 00EQ "right branch generator normal form"]
#check @AwayModuleGlueing.standard_target_right_lift_apply_mk_one
@[stacks 00EQ "triple-overlap inverse transport"]
#check @AwayModuleGlueing.triple_overlap_hom23_symm_apply
@[stacks 00EQ "left target branch normal form"]
#check @AwayModuleGlueing.localized_target_component_left_branch_normal_form
@[stacks 00EQ "right target branch normal form"]
#check @AwayModuleGlueing.localized_target_component_right_branch_normal_form
@[stacks 00EQ "left target branch generator comparison"]
#check @AwayModuleGlueing.localized_target_component_equiv_apply_left_branch_generator
@[stacks 00EQ "right target branch generator comparison"]
#check @AwayModuleGlueing.localized_target_component_equiv_apply_right_branch_generator

/- The source lifts are principal-open restrictions; these canonical owners remain the reusable
library surface even while the historical definitions above preserve their reduction behavior. -/
@[stacks 00EQ "canonical principal-open restriction"]
#check @LocalizedModule.Away.mapOfDvd
@[stacks 00EQ "canonical left principal-open restriction"]
#check @LocalizedModule.Away.Cech.restrictionLeft
@[stacks 00EQ "canonical right principal-open restriction"]
#check @LocalizedModule.Away.Cech.restrictionRight

end AwayModuleGlueing

end
