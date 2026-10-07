module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Category.Grp.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Fppf
namespace Big

/-- There exists a closed immersion of schemes whose big fppf pushforward on
abelian sheaves is not exact. -/
def existsNonexactPushforwardForClosedImmersion : Prop :=
  ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), IsClosedImmersion f ∧
    ¬ exactFunctor
      (Sheaf (Scheme.fppfTopology.over X) AddCommGrpCat.{u + 1})
      (Sheaf (Scheme.fppfTopology.over Y) AddCommGrpCat.{u + 1})
      ((Over.pullback f).sheafPushforwardContinuous (AddCommGrpCat.{u + 1})
        (Scheme.fppfTopology.over Y) (Scheme.fppfTopology.over X))

/-- The non-exactness proposition is equivalent to its explicit existential
specification over schemes, a closed immersion, and the induced pushforward. -/
theorem existsNonexactPushforwardForClosedImmersion_iff :
    existsNonexactPushforwardForClosedImmersion ↔
      ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), IsClosedImmersion f ∧
        ¬ exactFunctor
          (Sheaf (Scheme.fppfTopology.over X) AddCommGrpCat.{u + 1})
          (Sheaf (Scheme.fppfTopology.over Y) AddCommGrpCat.{u + 1})
          ((Over.pullback f).sheafPushforwardContinuous (AddCommGrpCat.{u + 1})
            (Scheme.fppfTopology.over Y) (Scheme.fppfTopology.over X)) := sorry

end Big
end Fppf
end Scheme
end AlgebraicGeometry
