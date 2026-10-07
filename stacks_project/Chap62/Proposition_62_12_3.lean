module

public import stacks_project.Chap62.Proposition_62_12_3_Bivariant

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

/-- Proposition 62.12.3: Let `(S, δ)` be as in the fibre-cycle action setup, and
let `f : X ⟶ Y` be a morphism of schemes locally of finite type over `S`. Let
`α` be a relative `r`-cycle on `X / Y`. For every cartesian square of a morphism
`g : Y' ⟶ Y` locally of finite type and every `k : ℤ`, the bivariant class
`bivariantClass δ f r α hα : BivariantClass δ f (-↑r)` acts on the Chow class
of a cycle `β` of `Y'` by the Chow class of `g^*α ∩ β`, after the canonical
degree transport `k - (-↑r) = k + r`. Here `g^*α` is
`FiberCycleFamily.baseChange` and the fibre-cycle action is `capOver`. -/
@[stacks 0H6F]
theorem bivariantClass_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsLocallyNoetherian Y.left]
    (r : ℕ) (α : CyclesOnFibers f.left r) (hα : IsRelative α)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ)
    (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) k) :
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
              (FiberCycleFamily.baseChange square α) k β))) :=
  sorry

end AlgebraicGeometry.RelativeCycle
