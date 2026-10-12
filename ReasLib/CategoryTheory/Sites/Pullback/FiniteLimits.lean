/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

@[expose] public section

open CategoryTheory Limits

universe v

namespace CategoryTheory.Functor

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- A functor between small sites preserving terminal objects and pullbacks is continuous
if and only if it preserves covering sieves. -/
theorem isContinuous_iff_coverPreserving_of_preservesTerminal_and_pullbacks
    [HasTerminal C] [HasPullbacks C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] :
    u.IsContinuous J K ↔ CoverPreserving J K u := sorry

namespace SheafPullback

/-- Pullback of type-valued sheaves along a continuous functor between small sites
preserves finite limits if the functor preserves terminal objects and pullbacks. -/
instance preservesFiniteLimitsOfTerminalAndPullbacks
    [HasTerminal C] [HasPullbacks C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K] :
    PreservesFiniteLimits (u.sheafPullback (Type v) J K) := sorry

end SheafPullback

end CategoryTheory.Functor
