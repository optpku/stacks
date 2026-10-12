/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products and pushforward for module presheaves

Pushforward along a morphism of commutative-ring presheaves is the composite of
precomposition, which is strong monoidal, and restriction of scalars, which is lax monoidal.
This file owns that composite structure and its basic comparison formulas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal

noncomputable section

universe u uC vC uD vD

namespace PresheafOfModules.Pushforward

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (F : C ⥤ D)
variable {O : Cᵒᵖ ⥤ CommRingCat.{u}} {O' : Dᵒᵖ ⥤ CommRingCat.{u}}
variable (b : O ⟶ F.op ⋙ O')

/-- The underlying morphism of ring presheaves defining module pushforward. -/
abbrev ringMap : ringPresheaf O ⟶ F.op ⋙ ringPresheaf O' :=
  PresheafOfModules.presheafStructureMap b

/-- The pointwise monoidal structure over a precomposed commutative-ring presheaf.
This instance is a definitional presentation bridge for typeclass search. -/
noncomputable instance precompMonoidalCategory :
    MonoidalCategory (PresheafOfModules.{u} (F.op ⋙ ringPresheaf O')) :=
  PresheafOfModules.monoidalCategory (R := F.op ⋙ O')

/-- Precomposition of module presheaves uses Mathlib's canonical strong-monoidal structure. -/
noncomputable instance pushforwardZeroMonoidal :
    (PresheafOfModules.pushforward₀.{u} F (ringPresheaf O')).Monoidal :=
  inferInstanceAs
    (PresheafOfModules.pushforward₀OfCommRingCat.{u} F O').Monoidal

/-- The restriction-of-scalars factor in module pushforward is canonically lax monoidal. -/
noncomputable instance restrictionLaxMonoidal :
    (PresheafOfModules.restrictScalars (ringMap F b)).LaxMonoidal :=
  PresheafOfModules.Restriction.functorLaxMonoidal
    (O := O) (O' := F.op ⋙ O') b

/-- Pushforward along a morphism of commutative-ring presheaves is canonically lax monoidal. -/
@[stacks 03EL "lax-monoidal module pushforward"]
noncomputable instance laxMonoidal :
    (PresheafOfModules.pushforward.{u} (ringMap F b)).LaxMonoidal :=
  inferInstanceAs
    ((PresheafOfModules.pushforward₀.{u} F (ringPresheaf O') ⋙
      PresheafOfModules.restrictScalars (ringMap F b)).LaxMonoidal)

/-- The lax unit comparison for pushforward of module presheaves. -/
noncomputable abbrev unitComparison :
    𝟙_ (PresheafOfModules.{u} (ringPresheaf O)) ⟶
      (PresheafOfModules.pushforward.{u} (ringMap F b)).obj
        (𝟙_ (PresheafOfModules.{u} (ringPresheaf O'))) :=
  ε (PresheafOfModules.pushforward.{u} (ringMap F b))

/-- The pushforward unit comparison is the composite of the restriction and precomposition
unit comparisons. -/
theorem unitComparison_eq :
    unitComparison F b =
      ε (PresheafOfModules.restrictScalars (ringMap F b)) ≫
        (PresheafOfModules.restrictScalars (ringMap F b)).map
          (ε (PresheafOfModules.pushforward₀.{u} F (ringPresheaf O'))) := sorry

/-- The lax tensor comparison for pushforward of module presheaves. -/
noncomputable abbrev tensorComparison
    (M N : PresheafOfModules.{u} (ringPresheaf O')) :
    (PresheafOfModules.pushforward.{u} (ringMap F b)).obj M ⊗
        (PresheafOfModules.pushforward.{u} (ringMap F b)).obj N ⟶
      (PresheafOfModules.pushforward.{u} (ringMap F b)).obj (M ⊗ N) :=
  μ (PresheafOfModules.pushforward.{u} (ringMap F b)) M N

/-- The pushforward tensor comparison is the composite of the restriction and precomposition
tensor comparisons. -/
theorem tensorComparison_eq
    (M N : PresheafOfModules.{u} (ringPresheaf O')) :
    tensorComparison F b M N =
      μ (PresheafOfModules.restrictScalars (ringMap F b))
          ((PresheafOfModules.pushforward₀.{u} F (ringPresheaf O')).obj M)
          ((PresheafOfModules.pushforward₀.{u} F (ringPresheaf O')).obj N) ≫
        (PresheafOfModules.restrictScalars (ringMap F b)).map
          (μ (PresheafOfModules.pushforward₀.{u} F (ringPresheaf O')) M N) := sorry

end PresheafOfModules.Pushforward
