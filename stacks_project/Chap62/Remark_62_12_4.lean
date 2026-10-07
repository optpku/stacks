module

public import stacks_project.Chap62.Remark_62_12_4_CapFamily

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RelativeCycle

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Remark 62.12.4: Let `(S, δ)` be as in Section 62.11. Let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`. Let `r ≥ 0`. A cycle-level
action `c : Action δ f r` assigns to every locally finite type `g : Y' ⟶ Y`
and every `e : ℤ` an operation `capAlong δ c g e` from `Z_e(Y')` to
`Z_{r+e}(Y' ×_Y X)`, compatible with proper pushforward, flat pullback, and
trivial-restriction Gysin as in Lemma 62.12.2. Then there is a relative
`r`-cycle `α` on `X / Y` such that `capAlong δ c g e` agrees with
`CyclesOnFibers.cap` of `FiberCycleFamily.baseChange` of `α` along the chosen
fibre product, for every such `g`. -/
@[stacks 0H6G]
theorem exists_of_action
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (c : Action δ f r) :
    ∃ α : Family f.left r,
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
                β) :=
  sorry

end AlgebraicGeometry.RelativeCycle
