module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.LineBundle.ZeroSection

/-!
# Chow maps for the zero section of an associated line bundle

This file defines proper pushforward and the transported Cartier--Gysin pullback for the
zero section of an associated line bundle, together with their Chern-class formulas.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.AssociatedVectorBundle

open Scheme.AssociatedVectorBundle

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable (δ : S → ℤ) [IsDimensionFunction δ]
variable (X : Over S) [LocallyOfFiniteType X.hom]
variable (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
variable (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
variable [Scheme.IsRelativeSpectrumOver P]

/-- Proper pushforward along the zero section in degree `k`. -/
noncomputable def pushforward (k : ℤ) :
    RelativeChow δ X k →+
      @RelativeChow S inferInstance δ inferInstance (totalOver X ℒ P)
        (totalOver_locallyOfFiniteType X ℒ P) k :=
  @ChowGroup.map S inferInstance δ inferInstance X (totalOver X ℒ P)
    inferInstance (totalOver_locallyOfFiniteType X ℒ P) (zeroSectionOver X ℒ P)
    (zeroSectionOver_isProper X ℒ P) k

/-- `pushforward` is the proper Chow pushforward along `zeroSectionOver`. -/
theorem pushforward_def (k : ℤ) :
    pushforward δ X ℒ P k =
      @ChowGroup.map S inferInstance δ inferInstance X (totalOver X ℒ P)
        inferInstance (totalOver_locallyOfFiniteType X ℒ P) (zeroSectionOver X ℒ P)
        (zeroSectionOver_isProper X ℒ P) k := sorry

/-- Gysin pullback along a regular zero scheme, transported through a compatible
identification of that zero scheme with the base. -/
noncomputable def gysinAt
    (σ : (inverseLine X ℒ P).sections)
    (h_regular : RingedSpace.IsRegularSection (inverseLine X ℒ P) σ)
    (e : X ≅ zeroSchemeOver X ℒ P σ)
    (h_e : e.hom.left ≫
        @Scheme.zeroSchemeι (totalOver X ℒ P).left _ (inverseLine X ℒ P)
          (Scheme.Modules.Invertible.tensorRight_isEquivalence
            (inverseLine_invertible X ℒ P)) σ =
      zeroSection X ℒ P) (n : ℤ) :
    @RelativeChow S inferInstance δ inferInstance (totalOver X ℒ P)
        (totalOver_locallyOfFiniteType X ℒ P) n →+
      RelativeChow δ X (n - 1) :=
  (@ChowGroup.map S inferInstance δ inferInstance (zeroSchemeOver X ℒ P σ) X
      (zeroSchemeOver_locallyOfFiniteType X ℒ P σ) inferInstance e.inv inferInstance
      (n - 1)).comp
    (@ChowGroup.gysin S inferInstance δ inferInstance (totalOver X ℒ P)
      (totalOver_locallyOfFiniteType X ℒ P) (inverseLine X ℒ P)
      (inverseLine_invertible X ℒ P) σ n)

/-- `gysinAt` is zero-scheme Gysin followed by transport through `e.symm`. -/
theorem gysinAt_def
    (σ : (inverseLine X ℒ P).sections)
    (h_regular : RingedSpace.IsRegularSection (inverseLine X ℒ P) σ)
    (e : X ≅ zeroSchemeOver X ℒ P σ)
    (h_e : e.hom.left ≫
        @Scheme.zeroSchemeι (totalOver X ℒ P).left _ (inverseLine X ℒ P)
          (Scheme.Modules.Invertible.tensorRight_isEquivalence
            (inverseLine_invertible X ℒ P)) σ =
      zeroSection X ℒ P) (n : ℤ) :
    gysinAt δ X ℒ P σ h_regular e h_e n =
      (@ChowGroup.map S inferInstance δ inferInstance (zeroSchemeOver X ℒ P σ) X
        (zeroSchemeOver_locallyOfFiniteType X ℒ P σ) inferInstance e.inv inferInstance
        (n - 1)).comp
        (@ChowGroup.gysin S inferInstance δ inferInstance (totalOver X ℒ P)
          (totalOver_locallyOfFiniteType X ℒ P) (inverseLine X ℒ P)
          (inverseLine_invertible X ℒ P) σ n) := sorry

/-- The degree-normalized Gysin component from degree `k + 1` on the total space to
degree `k` on the base. -/
noncomputable def pullback
    (σ : (inverseLine X ℒ P).sections)
    (h_regular : RingedSpace.IsRegularSection (inverseLine X ℒ P) σ)
    (e : X ≅ zeroSchemeOver X ℒ P σ)
    (h_e : e.hom.left ≫
        @Scheme.zeroSchemeι (totalOver X ℒ P).left _ (inverseLine X ℒ P)
          (Scheme.Modules.Invertible.tensorRight_isEquivalence
            (inverseLine_invertible X ℒ P)) σ =
      zeroSection X ℒ P) (k : ℤ) :
    @RelativeChow S inferInstance δ inferInstance (totalOver X ℒ P)
        (totalOver_locallyOfFiniteType X ℒ P) (k + 1) →+
      RelativeChow δ X k :=
  (@ChowGroup.reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance
      ((k + 1) - 1) k (add_sub_cancel_right k 1)).toAddMonoidHom.comp
    (gysinAt δ X ℒ P σ h_regular e h_e (k + 1))

/-- `pullback` is the degree-normalized component of `gysinAt`. -/
theorem pullback_def
    (σ : (inverseLine X ℒ P).sections)
    (h_regular : RingedSpace.IsRegularSection (inverseLine X ℒ P) σ)
    (e : X ≅ zeroSchemeOver X ℒ P σ)
    (h_e : e.hom.left ≫
        @Scheme.zeroSchemeι (totalOver X ℒ P).left _ (inverseLine X ℒ P)
          (Scheme.Modules.Invertible.tensorRight_isEquivalence
            (inverseLine_invertible X ℒ P)) σ =
      zeroSection X ℒ P) (k : ℤ) :
    pullback δ X ℒ P σ h_regular e h_e k =
      (@ChowGroup.reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance
        ((k + 1) - 1) k (add_sub_cancel_right k 1)).toAddMonoidHom.comp
        (gysinAt δ X ℒ P σ h_regular e h_e (k + 1)) := sorry

/-- Capping with the first Chern class and then pulling back to the associated line
bundle, with the target degree canonically reindexed. -/
noncomputable def firstChernClassCapThenPullback (k : ℤ) :
    RelativeChow δ X k →+
      @RelativeChow S inferInstance δ inferInstance (totalOver X ℒ P)
        (totalOver_locallyOfFiniteType X ℒ P) k :=
  (@ChowGroup.reindex (totalOver X ℒ P).left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ (totalOver X ℒ P).hom
        (totalOver_locallyOfFiniteType X ℒ P) inferInstance)
      ((totalOver X ℒ P).hom.relativeDimensionFunction δ)
      (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _
        (totalOver X ℒ P).hom inferInstance (totalOver_locallyOfFiniteType X ℒ P)
        δ inferInstance)
      ((k - 1) + 1) k (sub_add_cancel k 1)).toAddMonoidHom.comp
    ((@ChowGroup.flatPullback S inferInstance δ inferInstance (totalOver X ℒ P) X
      (totalOver_locallyOfFiniteType X ℒ P) inferInstance (projection X ℒ P) 1
      (projection_flat X ℒ P) (projection_relativeDimension X ℒ P) (k - 1)).comp
        (@ChowGroup.firstChernClassCap S inferInstance δ inferInstance X inferInstance ℒ
          inferInstance k))

/-- `firstChernClassCapThenPullback` is flat pullback after first-Chern cap, followed by
canonical degree transport. -/
theorem firstChernClassCapThenPullback_def (k : ℤ) :
    firstChernClassCapThenPullback δ X ℒ P k =
      (@ChowGroup.reindex (totalOver X ℒ P).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ (totalOver X ℒ P).hom
          (totalOver_locallyOfFiniteType X ℒ P) inferInstance)
        ((totalOver X ℒ P).hom.relativeDimensionFunction δ)
        (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _
          (totalOver X ℒ P).hom inferInstance (totalOver_locallyOfFiniteType X ℒ P)
          δ inferInstance)
        ((k - 1) + 1) k (sub_add_cancel k 1)).toAddMonoidHom.comp
          ((@ChowGroup.flatPullback S inferInstance δ inferInstance
            (totalOver X ℒ P) X (totalOver_locallyOfFiniteType X ℒ P) inferInstance
            (projection X ℒ P) 1 (projection_flat X ℒ P)
            (projection_relativeDimension X ℒ P) (k - 1)).comp
              (@ChowGroup.firstChernClassCap S inferInstance δ inferInstance X
                inferInstance ℒ inferInstance k)) := sorry

/-- Pullback along the zero section is a left inverse to flat pullback along the
associated line-bundle projection. -/
theorem pullback_comp_flatPullback
    (σ : (inverseLine X ℒ P).sections)
    (h_regular : RingedSpace.IsRegularSection (inverseLine X ℒ P) σ)
    (e : X ≅ zeroSchemeOver X ℒ P σ)
    (h_e : e.hom.left ≫
        @Scheme.zeroSchemeι (totalOver X ℒ P).left _ (inverseLine X ℒ P)
          (Scheme.Modules.Invertible.tensorRight_isEquivalence
            (inverseLine_invertible X ℒ P)) σ =
      zeroSection X ℒ P) (k : ℤ) :
    (pullback δ X ℒ P σ h_regular e h_e k).comp
        (@ChowGroup.flatPullback S inferInstance δ inferInstance (totalOver X ℒ P) X
          (totalOver_locallyOfFiniteType X ℒ P) inferInstance (projection X ℒ P) 1
          (projection_flat X ℒ P) (projection_relativeDimension X ℒ P) k) =
      AddMonoidHom.id (RelativeChow δ X k) := sorry

/-- Pushforward along the zero section is the negative of first-Chern capping followed
by flat pullback to the associated line bundle. -/
theorem pushforward_eq_neg_firstChernClassCapThenPullback (k : ℤ) :
    pushforward δ X ℒ P k =
      -firstChernClassCapThenPullback δ X ℒ P k := sorry

/-- Gysin pullback after zero-section pushforward is negative capping with the first
Chern class of the original line bundle. -/
theorem gysinAt_comp_pushforward
    (σ : (inverseLine X ℒ P).sections)
    (h_regular : RingedSpace.IsRegularSection (inverseLine X ℒ P) σ)
    (e : X ≅ zeroSchemeOver X ℒ P σ)
    (h_e : e.hom.left ≫
        @Scheme.zeroSchemeι (totalOver X ℒ P).left _ (inverseLine X ℒ P)
          (Scheme.Modules.Invertible.tensorRight_isEquivalence
            (inverseLine_invertible X ℒ P)) σ =
      zeroSection X ℒ P) (k : ℤ) :
    (gysinAt δ X ℒ P σ h_regular e h_e k).comp
        (pushforward δ X ℒ P k) =
      -ChowGroup.firstChernClassCap δ X ℒ k := sorry

end AlgebraicGeometry.ChowGroup.AssociatedVectorBundle
