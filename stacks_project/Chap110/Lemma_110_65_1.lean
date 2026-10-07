module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective

/-!
# Being projective is not local on the base
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Lemma 110.65.1 (1): the morphism property of being projective is not Zariski local on the
base. -/
@[stacks 08J1]
theorem Projective.not_isZariskiLocalAtTarget :
    ¬ IsZariskiLocalAtTarget (@Projective : MorphismProperty Scheme.{u}) := sorry

/-- Lemma 110.65.1 (2): the morphism property of being quasi-projective is not Zariski local on
the base. -/
@[stacks 08J1]
theorem QuasiProjective.not_isZariskiLocalAtTarget :
    ¬ IsZariskiLocalAtTarget (@QuasiProjective : MorphismProperty Scheme.{u}) := sorry

/-- Lemma 110.65.1 (3): the morphism property of being projective is not fpqc local on the
base. -/
@[stacks 08J1]
theorem Projective.not_isLocalAtTargetFpqc :
    ¬ MorphismProperty.IsLocalAtTarget (@Projective : MorphismProperty Scheme.{u})
        Scheme.fpqcPrecoverage := sorry

/-- Lemma 110.65.1 (4): the morphism property of being quasi-projective is not fpqc local on the
base. -/
@[stacks 08J1]
theorem QuasiProjective.not_isLocalAtTargetFpqc :
    ¬ MorphismProperty.IsLocalAtTarget (@QuasiProjective : MorphismProperty Scheme.{u})
        Scheme.fpqcPrecoverage := sorry

/-- There exists a scheme morphism which is locally projective on the base but not projective. -/
theorem Projective.exists_locallyProjective_not_projective :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), LocallyProjective f ∧ ¬ Projective f := sorry

/-- There exists a scheme morphism which is locally quasi-projective on the base but not
quasi-projective. -/
theorem QuasiProjective.exists_locallyQuasiProjective_not_quasiProjective :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), LocallyQuasiProjective f ∧ ¬ QuasiProjective f := sorry

end AlgebraicGeometry
