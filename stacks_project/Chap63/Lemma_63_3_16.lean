module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek

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

/-- Lemma 63.3.16: if `f : X ⟶ Y` is a morphism of schemes which is separated
and locally of finite type, then the functor `etaleLowerShriek f` commutes with
direct sums. -/
@[stacks 0F56]
instance etaleLowerShriek_preservesCoproducts {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] {I : Type v} :
    PreservesColimitsOfShape (Discrete I) (etaleLowerShriek f) := sorry

end AlgebraicGeometry.Scheme.Etale

end
