/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Limits.Types.Products
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TopCat

universe u v

variable (X : TopCat.{u})

/-
The canonical constant-functor construction from Definition 6.3.2 supplies the singleton values
and restriction maps. Specializing `Functor.isTerminalConst` at the canonical terminal object
`Types.isTerminalPUnit` therefore expresses the source directly, without a parallel presheaf or
terminal-object wrapper; `IsTerminal.uniqueUpToIso` records the stated uniqueness consequence.
-/
/- Example 6.4.1 (1): the constant singleton-valued presheaf on `X` is a final object in the
category of set-valued presheaves on `X`. -/
@[stacks 006H "the singleton-valued presheaf is final"]
#check
  (Functor.isTerminalConst (Opens X)ᵒᵖ Types.isTerminalPUnit :
    IsTerminal ((Functor.const (Opens X)ᵒᵖ).obj (PUnit : Type v)))

/- Example 6.4.1 (2): any final set-valued presheaf on `X` is uniquely isomorphic to the constant
singleton-valued presheaf. -/
@[stacks 006H "the final presheaf is unique up to unique isomorphism"]
#check
  (fun {F : X.Presheaf (Type v)} (hF : IsTerminal F) =>
    hF.uniqueUpToIso (Functor.isTerminalConst (Opens X)ᵒᵖ Types.isTerminalPUnit))
