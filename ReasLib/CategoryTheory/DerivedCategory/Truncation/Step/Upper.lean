/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Piece
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Upper Successive-Truncation Steps

This module exposes the degree-`n` specialization of Mathlib's functorial
triangle `t.triangleLTLTGELT n (n + 1)`.  Its third term is compared with the
underlying object of the canonical bundled truncation piece; the homology
information remains in `DerivedCategory.Truncation.Piece`.

The object and morphism computations of the triangle are inherited directly
from the `@[simps]` API of `t.triangleLTLTGELT`, so no parallel projection API
is introduced here.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure

universe w v u

noncomputable section

namespace CategoryTheory.DerivedCategory.TruncLE.Step

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The functorial upper successive-truncation triangle in degree `n`, with
terms `τ<n`, `τ<n+1`, and the upper-first degree-`n` piece. -/
@[stacks 08J5]
noncomputable abbrev triangle (n : ℤ) :
    DerivedCategory 𝒜 ⥤ Triangle (DerivedCategory 𝒜) :=
  t.triangleLTLTGELT n (n + 1) (le_add_of_nonneg_right zero_le_one)

/-- Every upper successive-truncation triangle is distinguished. -/
@[stacks 08J5]
theorem triangle_distinguished (n : ℤ) (K : DerivedCategory 𝒜) :
    (triangle 𝒜 n).obj K ∈ distTriang (DerivedCategory 𝒜) := sorry

/-- The third term of the upper successive-truncation triangle is naturally
the underlying object of the canonical bundled degree-`n` piece. -/
@[stacks 08J5]
noncomputable def pieceIso (n : ℤ) (K : DerivedCategory 𝒜) :
    ((triangle 𝒜 n).obj K).obj₃ ≅
      (DerivedCategory.Concentrated.ι 𝒜 n).obj
        ((DerivedCategory.Truncation.Piece.functor 𝒜 n).obj K) :=
  (DerivedCategory.Truncation.Piece.upperIso 𝒜 n).app K

/-- `pieceIso` is the component of the canonical upper-first comparison from
`Truncation.Piece`. -/
@[simp, stacks 08J5]
theorem pieceIso_eq (n : ℤ) (K : DerivedCategory 𝒜) :
    pieceIso 𝒜 n K = (DerivedCategory.Truncation.Piece.upperIso 𝒜 n).app K := sorry

end CategoryTheory.DerivedCategory.TruncLE.Step

end
