module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of truncation-filtration realization maps

A chosen representative lift admits compatible truncation-filtration realizations over a Grothendieck source.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB uC vC

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace Realization

/-- Given a chosen representative lift, compatible truncation-filtration realizations and a map
carrying exactly that lift exist over a Grothendieck source. -/
@[stacks 0BKM "existence of a truncation realization map with prescribed lift"]
theorem existsMapOfLift [IsGrothendieckAbelian.{w} A]
    {K L : DerivedCategory A} (f : K ⟶ L) (l : DerivedCategory.Preimage.Lift f) :
    ∃ (S : Realization F K) (T : Realization F L),
      Nonempty {m : Map F f S T // m.lift = l} := sorry

/-- If a derived morphism admits a lift between the selected representatives, compatible
truncation-filtration realizations exist in a Grothendieck source.

The existence hypothesis is explicit because the selected derived representatives are not a
functorial choice.  Use `existsMapOfLift` when the resulting realization map must carry a prescribed
lift. -/
@[stacks 0BKM "existence of truncation-filtration realization maps"]
theorem existsMap [IsGrothendieckAbelian.{w} A]
    {K L : DerivedCategory A} (f : K ⟶ L)
    (h_lift : Nonempty (DerivedCategory.Preimage.Lift f)) :
    ∃ (S : Realization F K) (T : Realization F L),
      Nonempty (Map F f S T) := sorry

/-- A compatible truncation realization map exists exactly when the derived morphism admits a lift
between the selected representatives. -/
@[stacks 0BKM "characterization of truncation realization-map existence"]
theorem existsMap_iff_nonemptyLift [IsGrothendieckAbelian.{w} A]
    {K L : DerivedCategory A} (f : K ⟶ L) :
    (∃ (S : Realization F K) (T : Realization F L), Nonempty (Map F f S T)) ↔
      Nonempty (DerivedCategory.Preimage.Lift f) := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
