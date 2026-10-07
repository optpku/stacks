module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_33_3_Gysin
public import stacks_project.Chap42.Lemma_42_35_3_Vanishing
public import stacks_project.Chap42.Lemma_42_54_9_GradedAlgebra
public import stacks_project.Chap42.Lemma_42_54_9_NormalCone

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.NormalCone

open AlgebraicGeometry.Scheme

/-- Lemma 42.54.9: for nested closed subschemes `Z ⊆ Y ⊆ X`, with `Y` and `Z`
effective Cartier divisors in the integral scheme `X`, zero-section Gysin pullback sends the
degree-`n` fundamental class of `C_Z X` to the degree-`n - 1` fundamental class of `C_Z Y`
in the cartesian fiber product. -/
@[stacks 0FEB]
theorem zeroSection_pullback_fundamental
    {S X Y Z : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion i]
    [IsEffectiveCartierDivisor j] [IsEffectiveCartierDivisor (i ≫ j)]
    [LocallyOfFiniteType j]
    (n : ℤ) (hX : p.relativeDimensionFunction delta (genericPoint X) = n)
    (PZY : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver PZY]
    (PZX : RelativeSpectrumOver (ConormalAlgebra.total (i ≫ j)))
    [IsRelativeSpectrumOver PZX]
    (PNY : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf j)))
    [hPNY : IsRelativeSpectrumOver PNY]
    (sigma : (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
      (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
      PNY hPNY).sections)
    (h_regular : RingedSpace.IsRegularSection
      (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
        (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
        PNY hPNY) sigma)
    (e : Over.mk (j ≫ p) ≅ @AssociatedVectorBundle.zeroSchemeOver _
      (Over.mk (j ≫ p)) (Hom.conormalSheaf j)
      (Scheme.NormalCone.conormalSheaf_invertible j) PNY hPNY sigma)
    (h_e : e.hom.left ≫
      @Scheme.zeroSchemeι
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY).left _
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY)
        (Modules.Invertible.tensorRight_isEquivalence
          (@AssociatedVectorBundle.inverseLine_invertible _
            (Over.mk (j ≫ p)) (Hom.conormalSheaf j)
            (Scheme.NormalCone.conormalSheaf_invertible j) PNY hPNY)) sigma =
      @AssociatedVectorBundle.zeroSection _ (Over.mk (j ≫ p))
        (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
        PNY hPNY) :
    letI : LocallyOfFiniteType
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY).hom :=
      @AssociatedVectorBundle.totalOver_locallyOfFiniteType _
        (Over.mk (j ≫ p)) (Hom.conormalSheaf j)
        (Scheme.NormalCone.conormalSheaf_invertible j) PNY hPNY
        (locallyOfFiniteType_comp j p)
    letI : Modules.Invertible
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY) :=
      @AssociatedVectorBundle.inverseLine_invertible _
        (Over.mk (j ≫ p)) (Hom.conormalSheaf j)
        (Scheme.NormalCone.conormalSheaf_invertible j) PNY hPNY
    ((BivariantClass.gysin delta
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY)
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY)
        sigma).cap
      (Scheme.NormalCone.toZeroSchemeOver p i j PZY PNY sigma e)
      (Scheme.NormalCone.toAmbientOver p i j PZY PZX)
      (Scheme.NormalCone.toNormalBundleOver p i j PZX PNY)
      (Scheme.NormalCone.fiberSquare p i j PZY PZX PNY sigma e h_e) n)
      (ChowGroup.fundamentalClass
        ((Scheme.NormalCone.over (i ≫ j ≫ p) (i ≫ j) PZX).hom
          |>.relativeDimensionFunction delta) n) =
    ChowGroup.fundamentalClass
      ((Scheme.NormalCone.over (i ≫ j ≫ p) i PZY).hom
        |>.relativeDimensionFunction delta) (n - 1) := sorry

end AlgebraicGeometry.ChowGroup.NormalCone
