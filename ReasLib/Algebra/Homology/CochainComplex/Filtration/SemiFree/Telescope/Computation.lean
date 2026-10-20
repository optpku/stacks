module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Telescope

@[expose] public section

/-!
# Telescope-Augmentation Computations

This leaf records the cocone and augmentation formulas for the explicit
degreewise telescope lifts of a semi-free filtration.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CountableFromSequential

noncomputable section

universe u

namespace CochainComplex.SemiFreeFiltration

section

variable {A : Type u} [Ring A]
variable [HasColimitsOfShape ℕ (ModuleCat.DGMod A)]

/-- The recursive degreewise stage lifts form a cocone on the evaluated filtration diagram. -/
theorem telescopeDegreewiseStageLift_naturality {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℤ) :
    ∀ k : ℕ,
      (F.toSequentialColimitFiltration.diagram ⋙
        HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).map
          (homOfLE (Nat.le_succ k)) ≫
        telescopeDegreewiseStageLift F n (k + 1) =
          telescopeDegreewiseStageLift F n k := sorry

/-- The `(k + 1)`st coproduct summand maps to the ambient module by the expected cocone leg
after the telescope augmentation. -/
theorem sigmaLeg_comp_telescopeAugmentation {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℤ) (k : ℕ) :
    ((Limits.Sigma.ι F.toSequentialColimitFiltration.diagram.obj (k + 1)).f n) ≫
        ((F.toSequentialColimitFiltration.telescopeShortComplex.g).f n) =
      (F.coconeApp (k + 1)).f n := sorry

/-- Applying the telescope augmentation after a degreewise stage lift recovers the corresponding
ambient cocone leg. -/
theorem telescopeDegreewiseStageLift_compAugmentation {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℤ) :
    ∀ k : ℕ,
      telescopeDegreewiseStageLift F n k ≫
          ((F.toSequentialColimitFiltration.telescopeShortComplex.g).f n) =
        (F.coconeApp k).f n := sorry

/-- The degreewise stage lifts define a cocone with apex the telescope coproduct. -/
noncomputable def telescopeDegreewiseLiftCocone {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℤ) :
    Cocone (F.toSequentialColimitFiltration.diagram ⋙
      HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n) :=
  Cocone.mk _ <|
    NatTrans.ofSequence
      (fun k ↦ telescopeDegreewiseStageLift F n k)
      (telescopeDegreewiseStageLift_naturality F n)

end

end CochainComplex.SemiFreeFiltration
