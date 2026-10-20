module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 82.10.1: In Situation 82.2.1, for good `X, Y / B`, a flat
morphism `f : X ⟶ Y` over `B` of relative dimension `r` induces the additive
map `f^* : Z_k(Y) → Z_{k+r}(X)` defined by locally finite sums of associated
cycles of scheme-theoretic inverse images. -/
@[stacks 0EP8]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullbackHom :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
      (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
      (hf : f ≫ pY = pX) (k : ℤ),
      Hom.cycleGroup pY δ k →+ Hom.cycleGroup pX δ (k + (r : ℤ)))

/- For an integral closed subspace `Z` of `δ`-dimension `k`, the pullback of
its generator is the associated `(k + r)`-cycle of its scheme-theoretic
inverse image, as justified by Lemma 82.9.1. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_integral :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
      (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
      (hf : f ≫ pY = pX) (k : ℤ) (Z : ClosedSubspace Y) [IsIntegral Z.X]
      (hZ : Hom.closedSubspaceDeltaDimension pY δ Z = (k : EInt)),
      Hom.flatPullback pY pX δ f r hf k
          (@ClosedSubspace.associatedCycle S Y
            (LocallyOfFiniteType.isLocallyNoetherian pY) Z
            (Hom.relativeDimensionFunction pY δ) k) =
        @ClosedSubspace.associatedCycle S X
          (LocallyOfFiniteType.isLocallyNoetherian pX) (Z.inverseImageSubspace f)
          (Hom.relativeDimensionFunction pX δ) (k + (r : ℤ)))

/- For `α = ∑ n_i [Z_i]`, the coefficients of `f^* α = ∑ n_i f^*[Z_i]`
are given by the locally finite sum below. Local finiteness is Lemma 82.9.2. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_apply :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
      (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
      (hf : f ≫ pY = pX) (k : ℤ) (α : Function.locallyFinsupp (Points Y) ℤ)
      (x : Points X),
      Hom.flatPullback pY pX δ f r hf k α x =
        ∑ᶠ y : Points Y,
          α y *
            (@ClosedSubspace.associatedCycle S X
              (LocallyOfFiniteType.isLocallyNoetherian pX)
              ((ClosedSubspace.pointClosure y).inverseImageSubspace f)
              (Hom.relativeDimensionFunction pX δ) (k + (r : ℤ)) x))
