module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Construction
public import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monic splittings of truncated simplicial objects

This module records when the chosen summands of a truncated splitting represent subobjects and
exposes both typeclass-driven and proof-form witnesses of splitness.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace Splitting

variable {n : ℕ} {X : SimplicialObject.Truncated C n} (s : Splitting X)

/-- A truncated splitting is monic when every distinguished summand map is a monomorphism. -/
@[stacks 017P "monic truncated splitting"]
class IsMonic : Prop where
  /-- Every distinguished truncated summand map is a monomorphism. -/
  mono (m : Fin (n + 1)) : Mono (s.ι m)

attribute [instance] IsMonic.mono

/-- The degree-`m` subobject represented by a monic truncated splitting. -/
@[stacks 017P "subobject represented by a truncated splitting"]
def subobject [s.IsMonic] (m : Fin (n + 1)) : Subobject (X _⦋m⦌ₙ) :=
  Subobject.mk (s.ι m)

end Splitting

/-- A truncated simplicial object is split in the source sense when it has a splitting whose
distinguished maps represent subobjects. -/
@[stacks 017P "existence of a truncated splitting by subobjects"]
def IsSplit {n : ℕ} (X : SimplicialObject.Truncated C n) : Prop :=
  ∃ s : Splitting X, s.IsMonic

namespace Splitting

/-- A chosen monic truncated splitting witnesses splitness of the underlying truncated simplicial
object. -/
@[stacks 017P "chosen monic truncated splitting witnesses splitness"]
theorem isSplit {n : ℕ} {X : SimplicialObject.Truncated C n} (s : Splitting X)
    [s.IsMonic] : IsSplit X := sorry

/-- A chosen truncated splitting witnesses splitness when monicity is supplied as an ordinary
proof.

This proof-form companion lets downstream users avoid installing a temporary instance for an
already established splitting property. -/
@[stacks 017P "splitness from an explicit monic truncated splitting proof"]
theorem isSplit_of_monic {n : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (hs : s.IsMonic) : IsSplit X := sorry

end Splitting

end CategoryTheory.SimplicialObject.Truncated
