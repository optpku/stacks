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
  sorry

/-- The identity inclusion induces the identity finite-stage ring homomorphism. -/
theorem stageMap_id (E : Finset A) :
    stageMap A (Finset.Subset.refl E) = RingHom.id (stage A E) :=
  sorry

/-- Finite-stage ring transitions compose along inclusions of finite subsets. -/
theorem stageMap_comp {E₁ E₂ E₃ : Finset A} (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃) :
    (stageMap A h₂₃).comp (stageMap A h₁₂) = stageMap A (h₁₂.trans h₂₃) :=
  sorry

/-- The canonical algebra transition associated to refinement of finite subsets. -/
noncomputable def algHom {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    stage A E₁ →ₐ[A] stage A E₂ where
  toRingHom := stageMap A h
  commutes' := stageMap_commutes h

/-- The identity subset induces the identity algebra map. -/
theorem algHom_id (E : Finset A) : algHom (Finset.Subset.refl E) = AlgHom.id A (stage A E) :=
  sorry

/-- Transition maps of stage algebras compose. -/
theorem algHom_comp {E₁ E₂ E₃ : Finset A} (h₁₂ : E₁ ⊆ E₂) (h₂₃ : E₂ ⊆ E₃) :
    (algHom h₂₃).comp (algHom h₁₂) = algHom (h₁₂.trans h₂₃) :=
  sorry

/-- Stage algebra maps commute with the structure maps from the base ring. -/
theorem algHom_commutes {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    (algHom h).comp (Algebra.ofId A (stage A E₁)) = Algebra.ofId A (stage A E₂) :=
  sorry

/-- Any algebra map between the specializing localizations of a pattern and its
restriction equals the canonical localization transition. -/
theorem specializingMap_unique {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) (p : Pattern A E₂)
    (f : specializingLocalization A (Pattern.restrict A E₁ p).elem
        (Pattern.restrict A E₁ p).span →ₐ[A]
      specializingLocalization A p.elem p.span) :
    f.toRingHom = specializingMap A h p :=
  sorry

/-- The covariant functor of stage algebras on finite subsets of a commutative ring. -/
noncomputable def ringFunctor (A : Type u) [CommRing A] : Finset A ⥤ CommRingCat.{u} where
  obj E := .of (stage A E)
  map f := CommRingCat.ofHom (stageMap A (leOfHom f))
  map_id E := congrArg CommRingCat.ofHom (stageMap_id E)
  map_comp f g :=
    congrArg CommRingCat.ofHom (stageMap_comp (leOfHom f) (leOfHom g)).symm

end Algebra.WLocalHull
