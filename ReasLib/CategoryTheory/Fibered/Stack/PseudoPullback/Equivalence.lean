/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ProjectionEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Local
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences in pseudopullbacks of stacks in groupoids

Equivalence of one cospan leg in a bilimit pseudopullback is detected by the opposite
projection. The stack-in-setoids closure is exposed first for an equivalence hypothesis, then
through a source-facing fully-faithful and locally-essentially-surjective criterion.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids

namespace PseudoPullback

variable {X Y Z : StackOver.Groupoids J}

/-- In a bilimit pseudopullback of stacks in groupoids, the second projection is an equivalence
over the base whenever the left cospan leg is an equivalence. -/
@[stacks 05W9 "pseudopullback projection equivalence"]
theorem sndIsEquivalence
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit] (hF : Hom.IsEquivalence F) :
    Hom.IsEquivalence P.snd := sorry

/-- The symmetric projection criterion for a bilimit pseudopullback. -/
@[stacks 05W9 "symmetric pseudopullback projection equivalence"]
theorem fstIsEquivalence
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit] (hG : Hom.IsEquivalence G) :
    Hom.IsEquivalence P.fst := sorry

namespace IsEquivalence

/-- If the left cospan leg is an equivalence and the bilimit apex is a stack in setoids, then
the right source is a stack in setoids. -/
@[stacks 05W9 "equivalence-leg setoid-stack closure"]
theorem rightInSetoids
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit] [IsStack.InSetoids J P.pt.p]
    (hF : Hom.IsEquivalence F) :
    IsStack.InSetoids J Y.p := sorry

/-- The symmetric closure statement for an equivalence on the right cospan leg. -/
@[stacks 05W9 "symmetric equivalence-leg setoid-stack closure"]
theorem leftInSetoids
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit] [IsStack.InSetoids J P.pt.p]
    (hG : Hom.IsEquivalence G) :
    IsStack.InSetoids J X.p := sorry

end IsEquivalence

namespace rightInSetoids

/-- Lemma 8.6.10 (tag 05W9): if the left cospan leg is fully faithful and locally essentially
surjective and the bilimit apex is a stack in setoids, then the right source is a stack in
setoids. -/
@[stacks 05W9]
theorem ofFullyFaithful
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit] [IsStack.InSetoids J P.pt.p]
    (hF : Nonempty (Hom.toBasedFunctor F).FullyFaithful)
    (hFess : Hom.LocallyEssentiallySurjective F) :
    IsStack.InSetoids J Y.p := sorry

end rightInSetoids

namespace leftInSetoids

/-- The symmetric fully-faithful and locally-essentially-surjective closure statement. -/
@[stacks 05W9 "symmetric"]
theorem ofFullyFaithful
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit] [IsStack.InSetoids J P.pt.p]
    (hG : Nonempty (Hom.toBasedFunctor G).FullyFaithful)
    (hGess : Hom.LocallyEssentiallySurjective G) :
    IsStack.InSetoids J X.p := sorry

end leftInSetoids

end PseudoPullback

end StackOver.Groupoids

end CategoryTheory
