/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.OverField
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Over a field, a bivariant class on `X ⟶ Spec k` commutes with every
bivariant class on a morphism `Y ⟶ Z` after the canonical product base change. -/
theorem commuteOfField
    {k : Type u} [Field k] {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (g : Y ⟶ Z) (p q : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p)
    (c' : BivariantClass (fun _ ↦ 0) g q) :
    Commute (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Z ⟶ Z) g
      (restrict (fun _ ↦ 0) (Limits.prod.fst : X ⨯ Z ⟶ X)
        (Limits.prod.snd : X ⨯ Z ⟶ Z) (terminal.from Z)
        (SchemeOverField.productIsPullback X (terminal.from Z)) p c) c' := sorry

end AlgebraicGeometry.BivariantClass
