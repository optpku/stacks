module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Compatibility
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.RepresentedHom

/-!
# Legacy Represented Hom Sequences for Derived Limits

The neutral owner of the represented-Hom towers and Milnor short exact sequence is
`CategoryTheory.HomotopyLimit.IsOf`. This leaf retains the historical `IsDerivedLimit` names as
a compatibility facade.
@stack 0919
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.IsDerivedLimit

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The compatibility name for the neutral represented-Hom tower
`HomotopyLimit.IsOf.homTower`. -/
abbrev homTower (Ksys : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  HomotopyLimit.IsOf.homTower Ksys L

/-- The compatibility name for the neutral shifted represented-Hom tower
`HomotopyLimit.IsOf.shiftedHomTower`. -/
abbrev shiftedHomTower (Ksys : SequentialInverseSystem D) (L : D) :
    SequentialInverseSystem (ModuleCat (End L)ᵐᵒᵖ) :=
  HomotopyLimit.IsOf.shiftedHomTower Ksys L

/-- Lemma 15.87.5 (Stacks 0919): compatibility form of the represented-Hom Milnor short exact
sequence for a legacy `IsDerivedLimit` witness. -/
@[stacks 0919]
theorem homShortExact
    {Ksys : SequentialInverseSystem D} {K : D}
    (hK : IsDerivedLimit Ksys K) (L : D) :
    ∃ (ι : DerivedLimit.R1 (shiftedHomTower Ksys L) ⟶
        (preadditiveCoyonedaObj L).obj K)
      (π : (preadditiveCoyonedaObj L).obj K ⟶ limit (homTower Ksys L))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end CategoryTheory.IsDerivedLimit

end
