module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.Tactic.CrossRefAttribute

/-!
# The terminal presheaf

This leaf names the constant singleton presheaf and its canonical terminal structure.  The
shared owner avoids repeating the implementation by `Functor.const` at every site-level use.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace Presheaf

/-- The terminal type-valued presheaf on a category. -/
@[stacks 09VU "terminal presheaf"]
abbrev terminal (C : Type u) [Category.{v} C] : Cᵒᵖ ⥤ Type w :=
  (Functor.const Cᵒᵖ).obj (PUnit : Type w)

/-- The constant singleton presheaf is terminal in the presheaf category. -/
def terminalIsTerminal (C : Type u) [Category.{v} C] :
    IsTerminal (terminal.{w} C) :=
  Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit

/-- The Yoneda presheaf represented by a terminal object is canonically the terminal presheaf. -/
@[stacks 09VU "terminal representable presheaf"]
noncomputable def yonedaTerminalIso
    {C : Type u} [Category.{v} C] (T : C) (hT : IsTerminal T) :
    yoneda.obj T ≅ terminal.{v} C :=
  (hT.isTerminalObj yoneda).uniqueUpToIso (terminalIsTerminal C)

end Presheaf

end CategoryTheory
