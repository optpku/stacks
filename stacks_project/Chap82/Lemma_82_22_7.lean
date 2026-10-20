module

public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap82.Definition_82_22_1_Gysin
public import stacks_project.Chap82.Lemma_82_6_3_AssociatedCycle

/-!
# Gysin pullback of closed-subspace cycles

On a good algebraic space, the refined Gysin map of a section of an invertible
module sends the cycle of a closed subspace to the cycle of its scheme-theoretic
intersection with the zero scheme, when that intersection is an effective
Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- The degree-`k` cycle of a closed subspace is a `k`-cycle. -/
theorem closedSubspaceCycle_mem (Z : ClosedSubspace X) (k : ℤ) :
    @ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Z
        ((Hom.relativeDimensionFunction (f)) δ) k ∈ (Hom.cycleGroup (f)) δ k :=
  sorry

/-- The associated cycle of the scheme-theoretic inverse image of a closed
subspace along `Z(s) ⟶ X` is a `k`-cycle on `Z(s)`. -/
theorem associatedCycle_inverseImage_mem (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (Z : ClosedSubspace X) (k : ℤ) :
    @ClosedSubspace.cycle S (zeroScheme L s).X
        (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f))
        (Z.inverseImage (zeroSchemeι L s))
        ((Hom.relativeDimensionFunction (zeroSchemeι L s ≫ f)) δ) k ∈
      (Hom.cycleGroup (zeroSchemeι L s ≫ f)) δ k :=
  sorry

/-- The Gysin cycle of `[Z]_{k+1}` equals the associated cycle of `D ∩ Z` on
`|D|`, when that intersection is an effective Cartier divisor on `Z`. -/
theorem gysinCycle_closedSubspaceCycle (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (Z : ClosedSubspace X) (k : ℤ)
    (hZ : (Hom.closedSubspaceDeltaDimension (f)) δ Z ≤ ((k + 1 : ℤ) : EInt))
    [IsEffectiveCartierDivisor ((zeroScheme L s).inverseImage Z.ι).ι] :
    gysinCycle f δ k L s
        (@ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Z
          ((Hom.relativeDimensionFunction (f)) δ) (k + 1)) =
      @ClosedSubspace.cycle S (zeroScheme L s).X
        (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f))
        (Z.inverseImage (zeroSchemeι L s))
        ((Hom.relativeDimensionFunction (zeroSchemeι L s ≫ f)) δ) k :=
  sorry

/-- Lemma 82.22.7: In Situation 82.2.1 let `X / B` be good. Let
`(L, s, i : D ⟶ X)` be as in Definition 82.22.1. Let `Z ⊂ X` be a closed
subspace such that `dim_δ(Z) ≤ k + 1` and such that `D ∩ Z` is an effective
Cartier divisor on `Z`. Then `i*([Z]_{k+1}) = [D ∩ Z]_k` in `CH_k(D)`. -/
@[stacks 0ER7]
theorem gysin_closedSubspaceCycle (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) (Z : ClosedSubspace X) (k : ℤ)
    (hZ : (Hom.closedSubspaceDeltaDimension (f)) δ Z ≤ ((k + 1 : ℤ) : EInt))
    [IsEffectiveCartierDivisor ((zeroScheme L s).inverseImage Z.ι).ι] :
    gysin f δ k L s
        ⟨@ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Z
            ((Hom.relativeDimensionFunction (f)) δ) (k + 1),
          closedSubspaceCycle_mem f δ Z (k + 1)⟩ =
      (Hom.chowMk (zeroSchemeι L s ≫ f)) δ k
        ⟨@ClosedSubspace.cycle S (zeroScheme L s).X
            (LocallyOfFiniteType.isLocallyNoetherian (zeroSchemeι L s ≫ f))
            (Z.inverseImage (zeroSchemeι L s))
            ((Hom.relativeDimensionFunction (zeroSchemeι L s ≫ f)) δ) k,
          associatedCycle_inverseImage_mem f δ L s Z k⟩ :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
