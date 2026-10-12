/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Complex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of strictly perfect complexes on ringed sites

Strict perfectness is intrinsic to a complex of modules on a ringed site. Its preservation by
pullback is therefore stated for bundled morphisms of ringed sites, independently of a chosen
commutative presentation or any derived-category construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{w}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (f : Hom X Y) [(f.modulePushforward.{w}).IsRightAdjoint]

namespace modulePullbackComplex

/-- Lemma 21.44.4: pullback along a morphism of ringed sites preserves strictly perfect
cochain complexes. -/
@[stacks 08H3]
theorem isStrictlyPerfect
    {E : CochainComplex (ModuleCat.{w} Y) ℤ}
    (hE : RingedSite.CochainComplex.IsStrictlyPerfect E) :
    RingedSite.CochainComplex.IsStrictlyPerfect
      ((f.modulePullbackComplex.{w}).obj E) := sorry

end modulePullbackComplex
end RingedSite.Hom
