module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Trunc
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Successive brutal truncations

This leaf owns the quotient piece and short exact row between two consecutive stages of the
canonical brutal truncation tower.  It is independent of derived categories and Postnikov
systems.
-/

@[expose] public section

open CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal.Trunc

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Piece

/-- The single complex supported at the cutoff of the `n`th brutal truncation. -/
@[stacks 0D8Z "single piece of a brutal truncation"]
noncomputable abbrev obj (K : CochainComplex A ℤ) (n : ℕ) : CochainComplex A ℤ :=
  (HomologicalComplex.single A (ComplexShape.up ℤ) (Brutal.Tower.index n)).obj
    (K.X (Brutal.Tower.index n))

/-- The map of cutoff pieces induced by a cochain map. -/
noncomputable abbrev map {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    obj K n ⟶ obj L n :=
  (HomologicalComplex.single A (ComplexShape.up ℤ) (Brutal.Tower.index n)).map
    (f.f (Brutal.Tower.index n))

/-- The cutoff-piece map of an identity is an identity. -/
@[simp, stacks 0D8Z]
theorem map_id (K : CochainComplex A ℤ) (n : ℕ) : map (𝟙 K) n = 𝟙 (obj K n) := sorry

/-- Cutoff-piece maps preserve composition. -/
@[simp, stacks 0D8Z]
theorem map_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n := sorry

/-- The cutoff belongs to the active range of its brutal truncation. -/
theorem cutoff_le (n : ℕ) : Brutal.Tower.index n ≤ Brutal.Tower.index n := sorry

/-- The active cutoff component satisfies the side condition for a map to a single complex. -/
theorem π_condition (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ)
    (hi : (ComplexShape.up ℤ).Rel i (Brutal.Tower.index n)) :
    (Trunc.obj K n).d i (Brutal.Tower.index n) ≫
      (StupidTrunc.activeIso K (Brutal.Tower.index n)
        (Brutal.Tower.index n) (cutoff_le n)).hom = 0 := sorry

/-- The canonical projection from a brutal stage to its newly exposed cutoff piece. -/
@[stacks 0D8Z "projection to a brutal truncation piece"]
noncomputable def π (K : CochainComplex A ℤ) (n : ℕ) : Trunc.obj K n ⟶ obj K n :=
  HomologicalComplex.mkHomToSingle
    (StupidTrunc.activeIso K (Brutal.Tower.index n)
      (Brutal.Tower.index n) (cutoff_le n)).hom
    (π_condition K n)

/-- At the cutoff, `π` is the active-stage identification followed by the single-object
identification. -/
@[simp, stacks 0D8Z]
theorem π_f_cutoff (K : CochainComplex A ℤ) (n : ℕ) :
    (π K n).f (Brutal.Tower.index n) =
      (StupidTrunc.activeIso K (Brutal.Tower.index n)
        (Brutal.Tower.index n) (cutoff_le n)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ)
          (Brutal.Tower.index n) (K.X (Brutal.Tower.index n))).inv := sorry

/-- Away from the cutoff, the projection to the single piece vanishes. -/
@[simp, stacks 0D8Z]
theorem π_f_of_ne (K : CochainComplex A ℤ) (n : ℕ) {i : ℤ}
    (hi : i ≠ Brutal.Tower.index n) : (π K n).f i = 0 := sorry

/-- Projection to the cutoff piece is natural in the cochain complex. -/
@[reassoc, stacks 0D8Z]
theorem π_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    Trunc.mapApp f n ≫ π L n = π K n ≫ map f n := sorry

end Piece

namespace Step

/-- A brutal transition followed by projection to the new cutoff piece is zero. -/
@[reassoc (attr := simp), stacks 0D8Z]
theorem step_comp_π (K : CochainComplex A ℤ) (n : ℕ) :
    Trunc.step K n ≫ Piece.π K (n + 1) = 0 := sorry

/-- Consecutive brutal stages and the newly exposed piece form a short complex. -/
@[stacks 0D8Z "successive brutal truncation row"]
noncomputable def shortComplex (K : CochainComplex A ℤ) (n : ℕ) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (Trunc.step K n) (Piece.π K (n + 1)) (step_comp_π K n)

/-- The short complex of consecutive brutal stages is short exact. -/
@[stacks 0D8Z "successive brutal truncation short exact sequence"]
theorem shortExact (K : CochainComplex A ℤ) (n : ℕ) :
    (shortComplex K n).ShortExact := sorry

end Step

end CategoryTheory.CochainComplex.Brutal.Trunc
