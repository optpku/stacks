/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Piece
public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Successive Lower-Truncation Steps

The step from `t.truncGE n` to `t.truncGE (n + 1)` is obtained by applying
Mathlib's canonical truncation triangle at `n + 1` after `t.truncGE n`.
Its first object is the canonical degree-`n` piece, while its third object is
naturally isomorphic to the unnested lower truncation at `n + 1`.

This module keeps the triangle functorial in the derived object.  It does not
replace the degree piece by a single complex using an inverse selected from a
deferred homology-isomorphism proof; the canonical homology cospan is exposed
separately by `DerivedCategory.Truncation.Piece`.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure

universe w v u

noncomputable section

namespace CategoryTheory.DerivedCategory.TruncGE.Step

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory.{w} 𝒜]

/-- The functorial lower-truncation step triangle in degree `n`, obtained by
applying the canonical triangle at `n + 1` to `t.truncGE n`. -/
@[stacks 08J5]
noncomputable abbrev triangle (n : ℤ) :
    DerivedCategory 𝒜 ⥤ Triangle (DerivedCategory 𝒜) :=
  t.truncGE n ⋙ t.triangleLTGE (n + 1)

/-- Every lower-truncation step triangle is distinguished. -/
@[stacks 08J5]
theorem triangle_distinguished (n : ℤ) (K : DerivedCategory 𝒜) :
    (triangle 𝒜 n).obj K ∈ distTriang (DerivedCategory 𝒜) := sorry

/-- The nested third term of the lower-truncation step is naturally the
unnested lower truncation at `n + 1`. -/
@[stacks 08J5]
noncomputable def targetIso (n : ℤ) :
    (DerivedCategory.TStructure.t (C := 𝒜)).truncGE n ⋙
        (DerivedCategory.TStructure.t (C := 𝒜)).truncGE (n + 1) ≅
      (DerivedCategory.TStructure.t (C := 𝒜)).truncGE (n + 1) :=
  ((DerivedCategory.TStructure.t (C := 𝒜)).eTruncGEIsoGEGE
    (n : EInt) ((n + 1 : ℤ) : EInt)
    (WithBotTop.coe_le_coe.mpr
      (le_add_of_nonneg_right zero_le_one))).symm

/-- The first term of the lower-truncation step is the underlying object of
the canonical bundled degree-`n` piece. -/
@[stacks 08J5]
noncomputable def pieceIso (n : ℤ) (K : DerivedCategory 𝒜) :
    ((triangle 𝒜 n).obj K).obj₁ ≅
      (DerivedCategory.Concentrated.ι 𝒜 n).obj
        ((DerivedCategory.Truncation.Piece.functor 𝒜 n).obj K) :=
  (DerivedCategory.Truncation.Piece.compιIso 𝒜 n).symm.app K

/-- The inverse component of `targetIso` is the canonical lower-truncation
map induced by the projection to `t.truncGE n`. -/
@[simp, stacks 08J5]
theorem targetIso_inv_app (n : ℤ) (K : DerivedCategory 𝒜) :
    (targetIso 𝒜 n).inv.app K =
      (t.truncGE (n + 1)).map ((t.truncGEπ n).app K) := sorry

/-- The component of `pieceIso` is inherited directly from the full-
subcategory lift of the canonical degree piece. -/
@[simp, stacks 08J5]
theorem pieceIso_eq (n : ℤ) (K : DerivedCategory 𝒜) :
    pieceIso 𝒜 n K =
      (DerivedCategory.Truncation.Piece.compιIso 𝒜 n).symm.app K := sorry

end CategoryTheory.DerivedCategory.TruncGE.Step

end
