module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory

@[expose] public section

/-!
# Fraction Calculi on Localized Full Subcategories

An ambient calculus of fractions restricts to a full subcategory when membership in its object
property is inherited in the direction in which the fraction construction introduces a new
object.  The hypotheses use mathlib's canonical `ObjectProperty.InheritedFromSource` and
`ObjectProperty.InheritedFromTarget` interfaces.
-/

universe v u

namespace CategoryTheory

open MorphismProperty ObjectProperty

variable {D : Type u} [Category.{v} D]
  (P : ObjectProperty D) (S : MorphismProperty D)

namespace ObjectProperty.InheritedFromSource

/-- Two-way invariance of `P` along `S` implies inheritance from the source. -/
theorem of_iff
    (hP : ∀ {X Y : D} (s : X ⟶ Y), S s → (P X ↔ P Y)) :
    P.InheritedFromSource S := sorry

end ObjectProperty.InheritedFromSource

namespace ObjectProperty.InheritedFromTarget

/-- Two-way invariance of `P` along `S` implies inheritance from the target. -/
theorem of_iff
    (hP : ∀ {X Y : D} (s : X ⟶ Y), S s → (P X ↔ P Y)) :
    P.InheritedFromTarget S := sorry

end ObjectProperty.InheritedFromTarget

namespace fullSubcategoryLocalizationSystem

/-- a left calculus of fractions restricts to a full subcategory whose object
property is inherited from denominator sources. -/
@[stacks 0GSL "left fractions in a localized full subcategory"]
instance hasLeftCalculusOfFractions [S.HasLeftCalculusOfFractions]
    [P.InheritedFromSource S] :
    (fullSubcategoryLocalizationSystem P S).HasLeftCalculusOfFractions := sorry

/-- a right calculus of fractions restricts to a full subcategory whose object
property is inherited from denominator targets. -/
@[stacks 0GSL "right fractions in a localized full subcategory"]
instance hasRightCalculusOfFractions [S.HasRightCalculusOfFractions]
    [P.InheritedFromTarget S] :
    (fullSubcategoryLocalizationSystem P S).HasRightCalculusOfFractions := sorry

/-- Two-way invariance along denominators is a convenient criterion for restricting a left
calculus of fractions. -/
theorem hasLeftCalculusOfFractions_of_mem_iff [S.HasLeftCalculusOfFractions]
    (hP : ∀ {X Y : D} (s : X ⟶ Y), S s → (P X ↔ P Y)) :
    (fullSubcategoryLocalizationSystem P S).HasLeftCalculusOfFractions := sorry

/-- Two-way invariance along denominators is a convenient criterion for restricting a right
calculus of fractions. -/
theorem hasRightCalculusOfFractions_of_mem_iff [S.HasRightCalculusOfFractions]
    (hP : ∀ {X Y : D} (s : X ⟶ Y), S s → (P X ↔ P Y)) :
    (fullSubcategoryLocalizationSystem P S).HasRightCalculusOfFractions := sorry

end fullSubcategoryLocalizationSystem


end CategoryTheory
