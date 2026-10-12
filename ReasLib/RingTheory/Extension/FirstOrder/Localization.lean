/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.FirstOrder
public import ReasLib.RingTheory.Extension.Localization
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of Universal First-Order Thickenings

This leaf treats localization in the target algebra while leaving the base
ring fixed.  Base-ring localization is the base-change theorem in
`ReasLib.RingTheory.Extension.FirstOrder.BaseChange`.

@stack 04EE
-/

@[expose] public section

noncomputable section

open Algebra

universe u v w x y

namespace Algebra.Extension.FirstOrder.IsUniversal

variable {R : Type u} {S : Type v} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
variable [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
variable {P : Extension.{w} R S}

section

variable (T : Submonoid S) [IsLocalization T S']

local notation "U" => T.comap (algebraMap P.Ring S)
local notation "Q" => (P.localization T : Extension R S')
local notation "L" => Localization U

private theorem localizationCore (hP : IsUniversal.{y} P) :
    IsUniversal.{y} Q := by
  have hcompat (a : P.Ring) :
      (IsScalarTower.toAlgHom R (Extension.Ring Q) S')
          (algebraMap P.Ring L a) =
        algebraMap S S' (algebraMap P.Ring S a) := by
    change algebraMap (Extension.Ring Q) S'
        ((Algebra.Extension.TargetLocalization.hom P T).toRingHom a) = _
    exact (Algebra.Extension.TargetLocalization.hom P T).algebraMap_toRingHom a
  refine ⟨?_, ?_⟩
  · rw [Algebra.Extension.TargetLocalization.ker_eq_map P T]
    rw [pow_two, ← Ideal.map_mul, ← pow_two, hP.squareZero, Ideal.map_bot]
  · intro A _ _ I hI f
    let f₀ : S →ₐ[R] A ⧸ I :=
      f.comp (IsScalarTower.toAlgHom R S S')
    obtain ⟨g, hg, huniq⟩ := hP.existsUniqueLiftAt I hI f₀
    have hunit : ∀ a : U, IsUnit (g a) := by
      intro a
      have hquot : IsUnit ((Ideal.Quotient.mkₐ R I) (g a)) := by
        have hmap :
            (Ideal.Quotient.mkₐ R I) (g a) =
              f (algebraMap S S' (algebraMap P.Ring S a)) := by
          simpa [f₀, AlgHom.comp_apply] using AlgHom.congr_fun hg a
        rw [hmap]
        exact (IsLocalization.map_units S'
          ⟨algebraMap P.Ring S a, a.2⟩).map f.toRingHom
      exact (IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩).mp <| by
        simpa [Ideal.Quotient.mkₐ_eq_mk] using hquot
    let g' : L →ₐ[R] A :=
      IsLocalization.liftAlgHom (M := U) (f := g) hunit
    have hg'_comp :
        g'.comp (Algebra.algHom R P.Ring L) = g := by
      ext a
      change IsLocalization.lift (M := U) (g := g.toRingHom) hunit
          (algebraMap P.Ring L a) = g a
      exact DFunLike.congr_fun
        (IsLocalization.lift_comp (M := U) (S := L)
          (g := g.toRingHom) hunit) a
    have hg' :
        (Ideal.Quotient.mkₐ R I).comp g' =
          f.comp (IsScalarTower.toAlgHom R (Extension.Ring Q) S') := by
      apply Localization.algHom_ext U
      ext a
      change (Ideal.Quotient.mkₐ R I)
          (g' (algebraMap P.Ring L a)) =
        f ((IsScalarTower.toAlgHom R (Extension.Ring Q) S')
          (algebraMap P.Ring L a))
      have hg'_comp_apply :
          g' (algebraMap P.Ring L a) = g a := by
        exact DFunLike.congr_fun hg'_comp a
      rw [hg'_comp_apply]
      calc
        (Ideal.Quotient.mkₐ R I) (g a) =
            f (algebraMap S S' (algebraMap P.Ring S a)) := by
          simpa [f₀, AlgHom.comp_apply] using AlgHom.congr_fun hg a
        _ = f ((IsScalarTower.toAlgHom R (Extension.Ring Q) S')
            (algebraMap P.Ring L a)) :=
          congrArg f (hcompat a).symm
    refine ⟨g', hg', ?_⟩
    intro g'' hg''
    have hg''source :
        (Ideal.Quotient.mkₐ R I).comp
            (g''.comp (Algebra.algHom R P.Ring L)) =
          f₀.comp (IsScalarTower.toAlgHom R P.Ring S) := by
      ext a
      calc
        (Ideal.Quotient.mkₐ R I)
            (g'' (algebraMap P.Ring L a)) =
            f ((IsScalarTower.toAlgHom R (Extension.Ring Q) S')
              (algebraMap P.Ring L a)) := by
          simpa [AlgHom.comp_apply] using
            AlgHom.congr_fun hg'' (algebraMap P.Ring L a)
        _ = f (algebraMap S S' (algebraMap P.Ring S a)) :=
          congrArg f (hcompat a)
    apply Localization.algHom_ext U
    exact (huniq _ hg''source).trans hg'_comp.symm

end

/-- Localizing the target of a universal first-order thickening preserves its
universal property. -/
@[stacks 04EE "(2), target localization of a universal first-order thickening"]
theorem localization (hP : IsUniversal.{y} P) (T : Submonoid S)
    [IsLocalization T S'] :
    IsUniversal.{y} (P.localization T : Extension R S') :=
  localizationCore T hP

end Algebra.Extension.FirstOrder.IsUniversal
