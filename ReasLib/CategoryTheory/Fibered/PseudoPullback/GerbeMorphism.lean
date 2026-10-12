/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.GerbeMorphism
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gerbe morphisms and explicit pseudo-pullbacks

Gerbe morphisms are stable under the explicit pseudo-pullback construction in `Cat/C`.  The
statements live at the heterogeneous `CartesianBasedFunctor` layer, so they apply before choosing
a fixed-universe bicategorical presentation or imposing stack conditions.
-/

@[expose] public section

universe uC vC uX vX uY vY uS vS

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable [X.p.IsFibered] [Y.p.IsFibered]

namespace CartesianBasedFunctor.IsGerbeMorphism

/-- The second projection from an explicit pseudo-pullback is a gerbe morphism when the first
leg of the defining cospan is one. -/
@[stacks 06P3 "base change of gerbe morphisms by explicit pseudo-pullbacks"]
theorem cartesianSnd
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor X.p S.p}
    [S.p.IsFibered]
    (hF : CartesianBasedFunctor.IsGerbeMorphism J F)
    (G : CartesianBasedFunctor Y.p S.p) :
    CartesianBasedFunctor.IsGerbeMorphism J
      (BasedCategory.PseudoPullback.cartesianSnd F G) := sorry

/-- A gerbe morphism is detected by its explicit pseudo-pullback along a locally essentially
surjective cartesian functor when the common target is fibred in groupoids. -/
@[stacks 06P4 "detecting gerbe morphisms by explicit pseudo-pullbacks"]
theorem of_cartesianSnd
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor X.p S.p}
    {G : CartesianBasedFunctor Y.p S.p} [Functor.IsFibered.InGroupoids S.p]
    (hG : CartesianBasedFunctor.LocallyEssentiallySurjective J G)
    (hSnd : CartesianBasedFunctor.IsGerbeMorphism J
      (BasedCategory.PseudoPullback.cartesianSnd F G)) :
    CartesianBasedFunctor.IsGerbeMorphism J F := sorry

end CartesianBasedFunctor.IsGerbeMorphism

namespace BasedCategory.PseudoPullback.cartesianSnd

/-- Under a locally essentially surjective base change into a groupoid-fibred target, the
explicit pseudo-pullback projection is a gerbe morphism exactly when the original functor is. -/
@[stacks 06P4 "gerbe morphisms and explicit pseudo-pullbacks"]
theorem isGerbeMorphism_iff
    {J : GrothendieckTopology C} (F : CartesianBasedFunctor X.p S.p)
    (G : CartesianBasedFunctor Y.p S.p) [Functor.IsFibered.InGroupoids S.p]
    (hG : CartesianBasedFunctor.LocallyEssentiallySurjective J G) :
    CartesianBasedFunctor.IsGerbeMorphism J
        (BasedCategory.PseudoPullback.cartesianSnd F G) ↔
      CartesianBasedFunctor.IsGerbeMorphism J F := sorry

end BasedCategory.PseudoPullback.cartesianSnd

end CategoryTheory
