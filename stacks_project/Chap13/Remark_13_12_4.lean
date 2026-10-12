/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.CategoryTheory.DerivedCategory.Truncation.Step.Upper
import ReasLib.CategoryTheory.DerivedCategory.Truncation.Step.Lower
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

-- Remark 13.12.4 (1): the canonical truncations of `K` fit into the distinguished triangle
-- `τ_{≤a} K ⟶ K ⟶ τ_{≥a+1} K ⟶ (τ_{≤a} K)[1]`.
@[stacks 08J5] #check @CategoryTheory.Triangulated.TStructure.triangleLEGE
@[stacks 08J5] #check @CategoryTheory.Triangulated.TStructure.triangleLEGE_distinguished

-- Remark 13.12.4 (2): the successive upper truncations of `K` fit into a distinguished triangle
-- whose third object is the degree-`n` piece.  The piece is bundled as a concentrated object,
-- hence is canonically a single object on its own degree-`n` homology.
@[stacks 08J5] #check @DerivedCategory.TruncLE.Step.triangle
@[stacks 08J5] #check @DerivedCategory.TruncLE.Step.triangle_distinguished
@[stacks 08J5] #check @DerivedCategory.TruncLE.Step.pieceIso
@[stacks 08J5] #check @DerivedCategory.Concentrated.inclusionIso

-- Remark 13.12.4 (3): the successive lower truncations of `K` fit into a distinguished triangle
-- whose first object is the same canonical degree-`n` piece.
@[stacks 08J5] #check @DerivedCategory.TruncGE.Step.triangle
@[stacks 08J5] #check @DerivedCategory.TruncGE.Step.triangle_distinguished
@[stacks 08J5] #check @DerivedCategory.TruncGE.Step.pieceIso
@[stacks 08J5] #check @DerivedCategory.TruncGE.Step.targetIso

-- Support for (2) and (3): both truncation orders yield the same degree piece, and its
-- degree-`n` homology is compared with `(DerivedCategory.homologyFunctor 𝒜 n).obj K` by a
-- cospan of canonical isomorphisms, without choosing inverse data.
@[stacks 08J5] #check @DerivedCategory.Truncation.Piece.upperIso
@[stacks 08J5] #check @DerivedCategory.Truncation.Piece.Homology.toGE
@[stacks 08J5] #check @DerivedCategory.Truncation.Piece.Homology.Bundled.toGE
@[stacks 08J5] #check @DerivedCategory.Truncation.Piece.Homology.toGE_isIso
@[stacks 08J5] #check @DerivedCategory.Truncation.Piece.Homology.Bundled.toGE_isIso
