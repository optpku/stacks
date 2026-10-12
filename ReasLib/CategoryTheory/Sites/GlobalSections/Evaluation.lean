/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global sections evaluated at a terminal object

This leaf compares a chosen global-sections functor with evaluation at an explicitly supplied
terminal object. It does not require the terminal object to be installed as ambient typeclass
data.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v uA vA

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C]

/-- Global sections are naturally isomorphic to sections over any explicitly supplied terminal
object. The global-sections functor remains the canonical right adjoint selected by
`HasGlobalSectionsFunctor`. -/
@[stacks 03YU "global sections evaluated at a terminal object"]
noncomputable def ΓNatIsoSheafSectionsOfTerminal
    (J : GrothendieckTopology C) (A : Type uA) [Category.{vA} A]
    [HasWeakSheafify J A] [HasGlobalSectionsFunctor J A]
    {T : C} (hT : IsTerminal T) :
    Γ J A ≅ (sheafSections J A).obj (op T) :=
  (constantSheafΓAdj J A).rightAdjointUniq (constantSheafAdj J A hT)

end CategoryTheory.Sheaf
