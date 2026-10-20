module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.NormalCone

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.NormalCone

open AlgebraicGeometry.Scheme

/-
Lemma 42.54.9: zero-section Gysin pullback sends the fundamental class of the ambient normal cone to the proper pushforward of the relative normal-cone fundamental class in the actual zero-section fiber.
-/
@[stacks 0FEB] #check (AlgebraicGeometry.ChowGroup.NormalCone.zeroSection_pullback_fundamental :
    ∀{S X Y Z : Scheme.{u}} [UniversallyCatenary S]
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
        PNY hPNY),
    -- Local instance justification (proof-local temporary data): supplies the derived conormal invertibility required by the normal-bundle comparison and Gysin construction.
    letI : Modules.Invertible (Hom.conormalSheaf j) :=
      Scheme.NormalCone.conormalSheaf_invertible j
    -- Local instance justification (proof-local temporary data): supplies the derived finite-type structure of the ambient normal cone required by the Gysin cap family and dimension function.
    letI : LocallyOfFiniteType (Scheme.NormalCone.over (i ≫ j ≫ p) (i ≫ j) PZX).hom :=
      Scheme.NormalCone.over_locallyOfFiniteType (i ≫ j ≫ p) (i ≫ j) PZX
    -- Local instance justification (proof-local temporary data): supplies the derived finite-type structure of the relative normal cone required by the Gysin cap family and dimension function.
    letI : LocallyOfFiniteType (Scheme.NormalCone.over (i ≫ j ≫ p) i PZY).hom :=
      Scheme.NormalCone.over_locallyOfFiniteType (i ≫ j ≫ p) i PZY
    -- Local instance justification (proof-local temporary data): supplies local Noetherianity of the ambient normal cone required to form its fundamental cycle.
    letI : IsLocallyNoetherian (Scheme.NormalCone.over (i ≫ j ≫ p) (i ≫ j) PZX).left :=
      Scheme.NormalCone.over_isLocallyNoetherian (i ≫ j ≫ p) (i ≫ j) PZX
    -- Local instance justification (proof-local temporary data): supplies local Noetherianity of the relative normal cone required to form its fundamental cycle.
    letI : IsLocallyNoetherian (Scheme.NormalCone.over (i ≫ j ≫ p) i PZY).left :=
      Scheme.NormalCone.over_isLocallyNoetherian (i ≫ j ≫ p) i PZY
    -- Local instance justification (proof-local temporary data): supplies local finite type of the normal-bundle comparison required by the Gysin cap family.
    letI : LocallyOfFiniteType (Scheme.NormalCone.toNormalBundleOver p i j PZX PNY).left :=
      Scheme.NormalCone.toNormalBundleOver_locallyOfFiniteType p i j PZX PNY
    -- Local instance justification (proof-local temporary data): supplies the derived finite-type structure required by the Gysin construction for this theorem.
    letI : LocallyOfFiniteType
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY).hom :=
      @AssociatedVectorBundle.totalOver_locallyOfFiniteType _
        (Over.mk (j ≫ p)) (Hom.conormalSheaf j)
        (Scheme.NormalCone.conormalSheaf_invertible j) PNY hPNY
        (locallyOfFiniteType_comp j p)
    -- Local instance justification (proof-local temporary data): supplies the derived invertibility structure required by the Gysin construction for this theorem.
    letI : Modules.Invertible
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY) :=
      @AssociatedVectorBundle.inverseLine_invertible _
        (Over.mk (j ≫ p)) (Hom.conormalSheaf j)
        (Scheme.NormalCone.conormalSheaf_invertible j) PNY hPNY
    -- Local instance justification (proof-local temporary data): supplies the derived finite-type structure of the actual zero-section fiber required by the Gysin cap family and proper pushforward.
    letI : LocallyOfFiniteType
        (Scheme.NormalCone.zeroSectionFiber p i j PZX PNY sigma).hom :=
      Scheme.NormalCone.zeroSectionFiber_locallyOfFiniteType p i j PZX PNY sigma
    -- Local instance justification (proof-local temporary data): supplies the canonical comparison's closed immersion, from which the properness required by Chow pushforward is inferred.
    letI : IsClosedImmersion
        (Scheme.NormalCone.toZeroSectionFiber p i j PZY PZX PNY sigma e h_e).left :=
      Scheme.NormalCone.toZeroSectionFiber_isClosedImmersion p i j PZY PZX PNY sigma e h_e
    ((BivariantClass.gysin delta
        (@AssociatedVectorBundle.totalOver _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY)
        (@AssociatedVectorBundle.inverseLine _ (Over.mk (j ≫ p))
          (Hom.conormalSheaf j) (Scheme.NormalCone.conormalSheaf_invertible j)
          PNY hPNY)
        sigma).cap
      (Scheme.NormalCone.zeroSectionFiberFst p i j PZX PNY sigma)
      (Scheme.NormalCone.zeroSectionFiberSnd p i j PZX PNY sigma)
      (Scheme.NormalCone.toNormalBundleOver p i j PZX PNY)
      (IsPullback.of_hasPullback _ _) n)
      (ChowGroup.fundamentalClass
        ((Scheme.NormalCone.over (i ≫ j ≫ p) (i ≫ j) PZX).hom
          |>.relativeDimensionFunction delta) n) =
    ChowGroup.map delta
      (Scheme.NormalCone.over (i ≫ j ≫ p) i PZY)
      (Scheme.NormalCone.zeroSectionFiber p i j PZX PNY sigma)
      (Scheme.NormalCone.toZeroSectionFiber p i j PZY PZX PNY sigma e h_e) (n - 1)
      (ChowGroup.fundamentalClass
        ((Scheme.NormalCone.over (i ≫ j ≫ p) i PZY).hom
          |>.relativeDimensionFunction delta) (n - 1))
)

end AlgebraicGeometry.ChowGroup.NormalCone
