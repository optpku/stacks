module

public import ReasLib.CategoryTheory.Adjunction.Abelian
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Adjunction

/-!
# Injective sheaves and sections with closed support

The closed-support functor preserves injective objects because its left adjoint, pushforward from
the closed subspace, preserves monomorphisms.  The functorial fact is registered once here so
downstream files do not need local instances or proof-specific adjunction setup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- Lemma 20.21.1 (0A3A), functorial form: sections supported on a closed subset preserve
injective objects. -/
@[stacks 0A3A "functorial form"]
noncomputable instance functorPreservesInjectiveObjects (hZ : IsClosed Z) :
    (functor (C := AddCommGrpCat.{u}) hZ).PreservesInjectiveObjects := sorry

/-- Lemma 20.21.1 (0A3A): sections supported on a closed subset of an injective abelian sheaf
form an injective abelian sheaf on that subset. -/
@[stacks 0A3A]
theorem injectiveObj
    (hZ : IsClosed Z) (ℐ : X.Sheaf AddCommGrpCat.{u}) (hℐ : Injective ℐ) :
    Injective ((functor (C := AddCommGrpCat.{u}) hZ).obj ℐ) := sorry

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport

end
