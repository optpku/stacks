/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

@[expose] public section

universe u

namespace SheafOfModules

/-- Module sheaves supported on a prescribed subset form a weak Serre class. -/
instance supportedOn_isWeakSerreClass {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u})
    (T : Set X) :
    CategoryTheory.ObjectProperty.IsWeakSerreClass (supportedOn (𝒪 := 𝒪) T) := sorry

end SheafOfModules
