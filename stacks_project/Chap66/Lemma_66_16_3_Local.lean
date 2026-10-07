module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Étale-local tests for morphisms of algebraic spaces

Étale-ness of a morphism of algebraic spaces is tested on a surjective étale
scheme atlas of the source, of the target, or on a commutative square of
scheme atlases.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Etale

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- There is a surjective étale morphism from a scheme to `X` whose composite
with `f` is étale as a morphism of algebraic spaces. -/
def existsOnSource : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧ Etale (φ ≫ f)

/-- `existsOnSource f` is the existence of a surjective étale scheme atlas of
`X` whose composite with `f` is étale. -/
theorem existsOnSource_iff : existsOnSource f ↔
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
          Etale (φ ≫ f) := sorry

namespace existsOnSource

/-- A surjective étale scheme atlas of `X` with étale composite with `f`
witnesses `existsOnSource f`. -/
theorem of {U : Over S} (φ : ofOver U ⟶ X)
    (h_etale : (over (@AlgebraicGeometry.Etale)).presheaf φ)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)
    [Etale (φ ≫ f)] : existsOnSource f := sorry

/-- `existsOnSource f` supplies a surjective étale scheme atlas of `X` whose
composite with `f` is étale. -/
theorem spec (h : existsOnSource f) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
          Etale (φ ≫ f) := sorry

end existsOnSource

/-- There is a surjective étale morphism from a scheme to `Y` along which every
base change of `f` is étale as a morphism of algebraic spaces. -/
def existsOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → Etale pV

/-- `existsOnTarget f` is the existence of a surjective étale scheme atlas of
`Y` along which pullbacks of `f` are étale. -/
theorem existsOnTarget_iff : existsOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) ψ ∧
          ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
            IsPullback pV pX ψ f → Etale pV := sorry

namespace existsOnTarget

/-- A surjective étale scheme atlas of `Y` with étale pullbacks of `f`
witnesses `existsOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y)
    (h_etale : (over (@AlgebraicGeometry.Etale)).presheaf ψ)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) ψ)
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Etale pV) : existsOnTarget f := sorry

/-- `existsOnTarget f` supplies a surjective étale scheme atlas of `Y` along
which pullbacks of `f` are étale. -/
theorem spec (h : existsOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) ψ ∧
          ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
            IsPullback pV pX ψ f → Etale pV := sorry

end existsOnTarget

/-- The chosen pullback projection `pullback.fst ψ f` is étale when `ψ` is a
surjective étale scheme atlas of `Y` along which every pullback of `f` is
étale. -/
theorem pullback_fst {V : Over S} (ψ : ofOver V ⟶ Y)
    (h_etale : (over (@AlgebraicGeometry.Etale)).presheaf ψ)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) ψ)
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Etale pV)
    [HasPullback ψ f] : Etale (pullback.fst ψ f) := sorry

/-- There is a commutative square of scheme atlases over `f` with étale
vertical arrows, surjective left vertical arrow, and étale horizontal
arrow. -/
def existsSquare : Prop :=
  ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : U ⟶ V),
    CommSq (ofOverMap h) φ ψ f ∧
      (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
          (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
            AlgebraicGeometry.Etale h.left

/-- `existsSquare f` is the existence of a commutative square of schemes over
`f` with étale vertical arrows, surjective left vertical arrow, and étale
horizontal arrow. -/
theorem existsSquare_iff : existsSquare f ↔
    ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : U ⟶ V),
      CommSq (ofOverMap h) φ ψ f ∧
        (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
            (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
              AlgebraicGeometry.Etale h.left := sorry

namespace existsSquare

/-- A commutative square of scheme atlases with étale vertical arrows,
surjective left vertical arrow, and étale horizontal arrow witnesses
`existsSquare f`. -/
theorem of {U V : Over S} {φ : ofOver U ⟶ X} {ψ : ofOver V ⟶ Y} {h : U ⟶ V}
    (sq : CommSq (ofOverMap h) φ ψ f)
    (hφ_etale : (over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hφ_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)
    (hψ_etale : (over (@AlgebraicGeometry.Etale)).presheaf ψ)
    [AlgebraicGeometry.Etale h.left] : existsSquare f := sorry

/-- `existsSquare f` supplies a commutative square of schemes over `f` with
étale vertical arrows, surjective left vertical arrow, and étale horizontal
arrow. -/
theorem spec (h : existsSquare f) :
    ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : U ⟶ V),
      CommSq (ofOverMap h) φ ψ f ∧
        (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
            (over (@AlgebraicGeometry.Etale)).presheaf ψ ∧
              AlgebraicGeometry.Etale h.left := sorry

end existsSquare

end Etale

end AlgebraicGeometry.AlgebraicSpace
