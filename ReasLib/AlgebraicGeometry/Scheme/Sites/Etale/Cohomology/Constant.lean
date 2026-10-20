module

public import ReasLib.CategoryTheory.Sites.SheafCohomology.ConstantPullback
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.ZMod
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Base change between small étale sites preserves finite limits. -/
instance smallEtalePullback_preservesFiniteLimits {S T : Scheme.{u}} (f : T ⟶ S) :
    PreservesFiniteLimits (smallEtalePullback f) :=
  CategoryTheory.preservesFiniteLimits_of_flat (smallEtalePullback f)

namespace Etale.Small

/-- The degree-`q` small étale cohomology group with constant `ZMod n` coefficients. -/
abbrev constantZModCohomology (X : Scheme.{u}) (n q : ℕ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    AddCommGrpCat.{u + 1} :=
  (Sheaf.functorH X.smallEtaleTopology q).obj
    (constantZModSheaf.{u + 1, u, u + 1} X.smallEtaleTopology n)

/-- A scheme morphism induces canonical pullback on small étale cohomology
with constant cyclic coefficients. -/
def constantZModCohomologyPullback {S T : Scheme.{u}} (f : T ⟶ S) (n q : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    constantZModCohomology S n q ⟶ constantZModCohomology T n q :=
  (smallEtalePullback f).constantCohomologyPullback.{u + 1, u, u + 1, u + 1}
    S.smallEtaleTopology T.smallEtaleTopology terminalIsTerminal
    (terminalIsTerminal.isTerminalObj (smallEtalePullback f) (⊤_ S.Etale))
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) q

end Etale.Small

end AlgebraicGeometry.Scheme
