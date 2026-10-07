module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap82.Definition_82_5_2_AssociatedCycle

/-!
# Étale pullback of an integral cycle

In the good setup of Situation 82.2.1, the associated cycle of the scheme-theoretic
inverse image of an integral closed subspace along an étale morphism is the
unweighted sum of the irreducible components of that inverse image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Set

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme-theoretic inverse image of an integral closed subspace along an
étale morphism of algebraic spaces is reduced. -/
instance instIsReduced_etaleInverseImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] (Z : ClosedSubspace Y) [IsIntegral Z.X] :
    IsReduced (Z.inverseImage f).X :=
  sorry

namespace ClosedSubspace

/-- Every irreducible component of the étale inverse image of an integral closed
subspace has multiplicity `1`. -/
theorem componentMultiplicity_etaleInverseImage {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [IsLocallyNoetherian X] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Etale f] (hf : f ≫ pY = pX) (Z : ClosedSubspace Y)
    [IsIntegral Z.X] (η : genericPoints (Z.inverseImage f).X) :
    componentMultiplicity (Z.inverseImage f) η = 1 :=
  sorry

end ClosedSubspace

namespace Hom

/-- Every generic point of the étale inverse image of an integral closed subspace
has the same relative dimension as the generic point of that subspace. -/
theorem deltaDimension_etaleInverseImage {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) [Etale f]
    (hf : f ≫ pY = pX) (Z : ClosedSubspace Y) [IsIntegral Z.X]
    (ξ : genericPoints Z.X) (η : genericPoints (Z.inverseImage f).X) :
    pX.relativeDimensionFunction δ (Points.map (Z.inverseImage f).ι η.1) =
      pY.relativeDimensionFunction δ (Points.map Z.ι ξ.1) :=
  sorry

/-- Lemma 82.10.3: In Situation 82.2.1 let `f : X ⟶ Y` be an étale morphism of
good algebraic spaces over `B`. If `Z ⊂ Y` is an integral closed subspace, then
`f^*[Z] = ∑ [Z']` where the sum is over the irreducible components
(Remark 82.5.1) of `f⁻¹(Z)`. The left-hand side is the associated cycle of
`Z.inverseImage f` at `k = dim_δ(Z)`, evaluated as the relative dimension of `Z`
at its generic point, and the right-hand side is the unweighted sum of
coefficients `1` at the images in `|X|` of `genericPoints` of `|f⁻¹(Z)|`. -/
@[stacks 0EPY]
theorem etalePullback_integral {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [IsLocallyNoetherian X] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Etale f] (hf : f ≫ pY = pX) (Z : ClosedSubspace Y)
    [IsIntegral Z.X] (ξ : genericPoints Z.X) (x : Points X) :
    ClosedSubspace.associatedCycle (Z.inverseImage f)
        (pX.relativeDimensionFunction δ)
        (pY.relativeDimensionFunction δ (Points.map Z.ι ξ.1)) x =
      @ite ℤ
        (x ∈ Points.map (Z.inverseImage f).ι '' genericPoints (Z.inverseImage f).X)
        (Classical.propDecidable _) 1 0 :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
