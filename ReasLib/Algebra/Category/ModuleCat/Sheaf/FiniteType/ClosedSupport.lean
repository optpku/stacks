/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType.Neighborhood
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed support of finite-type module sheaves

Finite type is a property of a module sheaf over a commutative-ring sheaf, so closedness of its
support is owned at that level rather than by bundled ringed spaces.
-/

@[expose] public section

open TopCat TopologicalSpace

universe u

namespace SheafOfModules.IsFiniteType

variable {X : TopCat.{u}} {𝒪 : X.Sheaf CommRingCat.{u}}

/-- Lemma 17.9.6 (01BA), module-sheaf owner: the support of a finite-type module sheaf over a
commutative-ring sheaf is closed. -/
@[stacks 01BA "module-sheaf owner"]
theorem isClosed_support
    (F : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)) [F.IsFiniteType] :
    IsClosed (SheafOfModules.support F) := sorry

end SheafOfModules.IsFiniteType
