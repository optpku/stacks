module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.Action

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RelativeCycle

noncomputable section

universe u

/- Remark 62.12.4: Every nonnegative-degree cycle-level action compatible with proper
pushforward, flat pullback, and trivial-restriction Gysin maps is induced by a relative
cycle on every locally finite type base change. -/
@[stacks 0H6G] #check (AlgebraicGeometry.RelativeCycle.exists_of_action :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (c : Action δ f r),
    ∃ α : f.left.FiberCycleFamily (r : ℤ),
      IsRelative α ∧
        ∀ {Y' : Over S} [LocallyOfFiniteType Y'.hom] (g : Y' ⟶ Y)
          [LocallyOfFiniteType g.left] (e : ℤ)
          (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) e),
          CycleGroup.toAlgebraicCycle
              ((pullback.snd f.left g.left ≫ Y'.hom).relativeDimensionFunction δ)
              ((r : ℤ) + e) (capAlong δ c g e β) =
            CycleGroup.toAlgebraicCycle
              ((pullback.snd f.left g.left ≫ Y'.hom).relativeDimensionFunction δ)
              ((r : ℤ) + e)
              (CyclesOnFibers.cap Y'.hom (pullback.snd f.left g.left) δ
                (FiberCycleFamily.baseChange
                  (IsPullback.of_hasPullback f.left g.left) α)
                β))
