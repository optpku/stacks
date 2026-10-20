module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.ValuativeCriterion

/-!
# Compatibility names for the valuative criterion on scheme presheaves
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- A valuative test for a presheaf on schemes over `B`. -/
abbrev ValuativeCommSq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) := SchemeOver.ValuativeCommSq F

/-- A dominating extension of a valuative test with a lifted presheaf point. -/
abbrev ValuativeCommSq.Extension {S : Scheme.{u}} {B : AlgebraicSpace S}
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (sq : ValuativeCommSq F) :=
  SchemeOver.ValuativeCommSq.Extension sq

/-- The existence part of the valuative criterion for a scheme presheaf. -/
abbrev ValuativeCriterion.Existence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) := SchemeOver.ValuativeCriterion.Existence F

end AlgebraicGeometry.AlgebraicSpace.Quot

/- The generic existence criterion quantifies over all valuative tests and
allows dominating extensions with a lift of the generic point. -/
#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.ValuativeCriterion.Existence :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}, ((SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) → Prop)
