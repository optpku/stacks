module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Failure of locality for projective and quasi-projective morphisms
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Projectivity of scheme morphisms is not Zariski local on the target. -/
theorem Projective.not_isZariskiLocalAtTarget :
    ¬ IsZariskiLocalAtTarget (@Projective : MorphismProperty Scheme.{u}) := sorry

/-- Quasi-projectivity of scheme morphisms is not Zariski local on the target. -/
theorem QuasiProjective.not_isZariskiLocalAtTarget :
    ¬ IsZariskiLocalAtTarget (@QuasiProjective : MorphismProperty Scheme.{u}) := sorry

/-- Projectivity of scheme morphisms is not local on the target for the fpqc precoverage. -/
theorem Projective.not_isLocalAtTargetFpqc :
    ¬ MorphismProperty.IsLocalAtTarget (@Projective : MorphismProperty Scheme.{u})
        Scheme.fpqcPrecoverage := sorry

/-- Quasi-projectivity of scheme morphisms is not local on the target for the fpqc precoverage. -/
theorem QuasiProjective.not_isLocalAtTargetFpqc :
    ¬ MorphismProperty.IsLocalAtTarget (@QuasiProjective : MorphismProperty Scheme.{u})
        Scheme.fpqcPrecoverage := sorry

/-- There is a scheme morphism which is locally projective on the target but not projective. -/
theorem Projective.exists_locallyProjective_not_projective :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), LocallyProjective f ∧ ¬ Projective f := sorry

/-- There is a scheme morphism which is locally quasi-projective on the target but not
quasi-projective. -/
theorem QuasiProjective.exists_locallyQuasiProjective_not_quasiProjective :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), LocallyQuasiProjective f ∧ ¬ QuasiProjective f := sorry

end AlgebraicGeometry
