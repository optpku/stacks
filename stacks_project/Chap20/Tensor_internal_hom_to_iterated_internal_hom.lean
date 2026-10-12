/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import StacksCheckRecall

@[expose] public section

/-!
# Source-order tensor/internal-Hom comparison

The reusable owner is `CategoryTheory.MonoidalClosed.Source.Iterated.map`.  This historical
Chapter 20 support file remains only as a compatibility recall for the chapter aggregate; the
construction and its specification live in ReasLib.
-/

open CategoryTheory
open CategoryTheory.MonoidalClosed

@[stacks 0A8U]
#check @CategoryTheory.MonoidalClosed.Source.Iterated.map

@[stacks 0A8U "tensor-side specification"]
#check @CategoryTheory.MonoidalClosed.Source.Iterated.map_spec

@[stacks 0A8U "uncurried specification"]
#check @CategoryTheory.MonoidalClosed.Source.Iterated.map_uncurry

end
