/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.Bivariant

/-!
# Bivariant class of a relative cycle

This file records that a relative `r`-cycle determines a degree `-r` bivariant
class whose cap action is the fibre-cycle operation `g^*α ∩ -`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Proposition 62.12.3: A relative cycle defines a bivariant class whose
cap action is the base-changed fibre-cycle action on cycle representatives. -/
@[stacks 0H6F] #check (AlgebraicGeometry.RelativeCycle.bivariantClass_apply :
  ∀
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ)
    (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) k),
    (bivariantClass δ f r α hα).cap i f' g square k
        (@chowClass Y'.left (LocallyOfFiniteType.isLocallyNoetherian Y'.hom)
          (Y'.hom.relativeDimensionFunction δ) inferInstance k β) =
      @ChowGroup.reindex X'.left
          (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
          (X'.hom.relativeDimensionFunction δ) inferInstance
          (k + (r : ℤ)) (k - (-(r : ℤ)))
          (sub_neg_eq_add k (r : ℤ)).symm
        (@chowClass X'.left (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
          (X'.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ))
          (CycleGroup.reindex (X'.hom.relativeDimensionFunction δ)
            (add_comm (r : ℤ) k)
            (CyclesOnFibers.capOver δ f'
              (FiberCycleFamily.baseChange square α) k β))))

end AlgebraicGeometry.RelativeCycle
