module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Represented Hom Sequences for Sequential Homotopy Limits

Applying `Hom(L, -)` to a sequential homotopy-limit triangle gives a Milnor short exact
sequence. This neutral leaf owns the represented-Hom towers and states the result in terms of
the presentation-independent predicate `HomotopyLimit.IsOf`.
@stack 0919
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit.IsOf

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The tower of represented Hom modules attached to a sequential inverse system and a test
object. -/
@[stacks 0919 "represented-Hom tower"]
abbrev homTower (K : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  K ⋙ preadditiveCoyonedaObj L

/-- The shifted represented-Hom tower controlling the first derived-limit term in the Milnor
sequence. -/
@[stacks 0919 "shifted represented-Hom tower"]
abbrev shiftedHomTower (K : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  (K ⋙ shiftFunctor D (-1 : ℤ)) ⋙ preadditiveCoyonedaObj L

/-- Lemma 15.87.5 (Stacks 0919): the represented Hom modules of a sequential homotopy limit
fit into the Milnor short exact sequence. -/
@[stacks 0919]
theorem homShortExact
    {Ksys : SequentialInverseSystem D} {K : D}
    (hK : HomotopyLimit.IsOf Ksys K) (L : D) :
    ∃ (ι : SequentialInverseSystem.Milnor.ProductCone.canonicalR1
          (shiftedHomTower Ksys L) ⟶ (preadditiveCoyonedaObj L).obj K)
      (π : (preadditiveCoyonedaObj L).obj K ⟶ limit (homTower Ksys L))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end CategoryTheory.HomotopyLimit.IsOf

end
