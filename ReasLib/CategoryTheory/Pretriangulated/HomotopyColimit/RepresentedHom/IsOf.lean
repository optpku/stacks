module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.ShortComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Intrinsic represented Hom sequence for a homotopy colimit

This leaf bridges the presentation-independent predicate `HomotopyColimit.IsOf` to the named
represented Hom short complex of an explicit presentation.
@stack 0CQX
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.IsOf

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
  [Pretriangulated D] [IsTriangulated D]

/-- Lemma 15.87.7 (Stacks 0CQX): an intrinsic sequential homotopy-colimit witness admits an
explicit presentation whose named represented Hom Milnor short complex is short exact. -/
@[stacks 0CQX]
theorem homShortExact {K : ℕ ⥤ D} {Khocolim : D}
    (hK : HomotopyColimit.IsOf K Khocolim) (L : D) :
    ∃ P : HomotopyColimit.Presentation K Khocolim,
      (HomotopyColimit.RepresentedHom.shortComplex P L).ShortExact := sorry

end CategoryTheory.HomotopyColimit.IsOf

end
