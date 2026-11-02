/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import ReasLib.Algebra.WLocalHull.WLocalization

/-!
# Transitions of finite vanishing-pattern algebras

Refinement of finite subsets induces canonical algebra maps between their
vanishing-pattern stages, forming a covariant system of commutative rings.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Algebra.WLocalHull

variable {A : Type u} [CommRing A]

/-- Finite-stage ring transitions preserve the algebra structure over the base ring. -/
theorem stageMap_commutes {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) (element : A) :
    stageMap A h (algebraMap A (stage A E₁) element) =
      algebraMap A (stage A E₂) element :=
  by
    funext p
    exact IsLocalization.map_eq (specializingSubmonoid_mono A h p) element

/-- The identity inclusion induces the identity finite-stage ring homomorphism. -/
theorem stageMap_id (E : Finset A) :
    stageMap A (Finset.Subset.refl E) = RingHom.id (stage A E) :=
  by
    classical
    apply RingHom.ext
    intro x
    funext p
    have hp : Pattern.restrict A E p = p := by
      apply Subtype.ext
      exact Finset.inter_eq_right.mpr p.property
    have map_id (q : Pattern A E) (hq : q = p)
        (hm : specializingSubmonoid A q.elem q.span ≤
          (specializingSubmonoid A p.elem p.span).comap (RingHom.id A)) :
        IsLocalization.map (specializingLocalization A p.elem p.span)
          (RingHom.id A) hm (x q) = x p := by
      subst q
      exact IsLocalization.map_id _ _
    exact map_id _ hp (specializingSubmonoid_mono A (Finset.Subset.refl E) p)

/-- Finite-stage ring transitions compose along inclusions of finite subsets. -/
theorem stageMap_comp {E₁ E₂ E₃ : Finset A} (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃) :
    (stageMap A h₂₃).comp (stageMap A h₁₂) = stageMap A (h₁₂.trans h₂₃) :=
  by
    classical
    apply RingHom.ext
    intro x
    funext p
    have hp : Pattern.restrict A E₁ (Pattern.restrict A E₂ p) =
        Pattern.restrict A E₁ p := by
      apply Subtype.ext
      change E₁ ∩ (E₂ ∩ p.1) = E₁ ∩ p.1
      rw [← Finset.inter_assoc, Finset.inter_eq_left.mpr h₁₂]
    change specializingMap A h₂₃ p
      (specializingMap A h₁₂ (Pattern.restrict A E₂ p)
        (x (Pattern.restrict A E₁ (Pattern.restrict A E₂ p)))) =
      specializingMap A (h₁₂.trans h₂₃) p (x (Pattern.restrict A E₁ p))
    dsimp only [specializingMap]
    rw [IsLocalization.map_map]
    have map_congr (q : Pattern A E₁) (hq : q = Pattern.restrict A E₁ p)
        (hm : specializingSubmonoid A q.elem q.span ≤
          (specializingSubmonoid A p.elem p.span).comap (RingHom.id A)) :
        IsLocalization.map (specializingLocalization A p.elem p.span)
          (RingHom.id A) hm (x q) =
          specializingMap A (h₁₂.trans h₂₃) p (x (Pattern.restrict A E₁ p)) := by
      subst q
      rfl
    exact map_congr _ hp _

/-- The canonical algebra transition associated to refinement of finite subsets. -/
noncomputable def algHom {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    stage A E₁ →ₐ[A] stage A E₂ where
  toRingHom := stageMap A h
  commutes' := stageMap_commutes h

/-- The identity subset induces the identity algebra map. -/
theorem algHom_id (E : Finset A) : algHom (Finset.Subset.refl E) = AlgHom.id A (stage A E) :=
  AlgHom.coe_ringHom_injective (stageMap_id E)

/-- Transition maps of stage algebras compose. -/
theorem algHom_comp {E₁ E₂ E₃ : Finset A} (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃) :
    (algHom h₂₃).comp (algHom h₁₂) = algHom (h₁₂.trans h₂₃) :=
  AlgHom.coe_ringHom_injective (stageMap_comp h₁₂ h₂₃)

/-- Stage algebra maps commute with the structure maps from the base ring. -/
theorem algHom_commutes {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    (algHom h).comp (Algebra.ofId A (stage A E₁)) = Algebra.ofId A (stage A E₂) :=
  AlgHom.ext (stageMap_commutes h)

/-- Any algebra map between the specializing localizations of a pattern and its
restriction equals the canonical localization transition. -/
theorem specializingMap_unique {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) (p : Pattern A E₂)
    (f : specializingLocalization A (Pattern.restrict A E₁ p).elem
        (Pattern.restrict A E₁ p).span →ₐ[A]
      specializingLocalization A p.elem p.span) :
    f.toRingHom = specializingMap A h p :=
  by
    apply IsLocalization.ringHom_ext
      (specializingSubmonoid A (Pattern.restrict A E₁ p).elem
        (Pattern.restrict A E₁ p).span)
    apply RingHom.ext
    intro element
    change f (algebraMap A _ element) = specializingMap A h p (algebraMap A _ element)
    rw [f.commutes]
    exact (IsLocalization.map_eq (specializingSubmonoid_mono A h p) element).symm

/-- The covariant functor of stage algebras on finite subsets of a commutative ring. -/
noncomputable def ringFunctor (A : Type u) [CommRing A] : Finset A ⥤ CommRingCat.{u} where
  obj E := .of (stage A E)
  map f := CommRingCat.ofHom (stageMap A (leOfHom f))
  map_id E := congrArg CommRingCat.ofHom (stageMap_id E)
  map_comp f g :=
    congrArg CommRingCat.ofHom (stageMap_comp (leOfHom f) (leOfHom g)).symm

end Algebra.WLocalHull
