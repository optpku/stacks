module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek

/-!
# Compact-support pushforward preserves direct sums
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- Compact-support pushforward along a separated, locally finite-type morphism
of schemes preserves arbitrary coproducts of abelian étale sheaves. -/
instance etaleLowerShriek_preservesCoproducts {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] {I : Type v} :
    PreservesColimitsOfShape (Discrete I) (etaleLowerShriek f) := sorry

end AlgebraicGeometry.Scheme.Etale

end
