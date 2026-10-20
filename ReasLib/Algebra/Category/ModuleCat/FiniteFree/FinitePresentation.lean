module

public import ReasLib.Algebra.Category.ModuleCat.FiniteFree
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-free modules are finitely presented

This bridge is separated from the basic finite-free object property so consumers that only need
freeness and finiteness do not import the filtered-colimit presentation API.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ModuleCat

variable (R : Type u) [Ring R]

/-- Finite-free bundled modules are finitely presented. -/
@[stacks 0GT1 "finite-free modules are finitely presented"]
theorem finiteFree_le_isFinitePresentation :
    finiteFree.{u, v} R ≤ _root_.ModuleCat.isFinitePresentation.{u, v} R := sorry

end CategoryTheory.ModuleCat
