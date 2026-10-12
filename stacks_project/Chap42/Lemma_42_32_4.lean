/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.LineBundle.ZeroSection
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.LineBundle.ZeroSection

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 42.32.4 (1): the zero section of the line bundle associated to `ℒ` is identified
with the zero scheme of a regular section of the pulled-back inverse line bundle. -/
@[stacks 0F96] #check
  (AlgebraicGeometry.Scheme.AssociatedVectorBundle.existsRegularZeroScheme :
    ∀ {S : Scheme.{u}} (X : Over S)
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [Scheme.IsRelativeSpectrumOver P],
      ∃ σ : (Scheme.AssociatedVectorBundle.inverseLine X ℒ P).sections,
        RingedSpace.IsRegularSection
            (Scheme.AssociatedVectorBundle.inverseLine X ℒ P) σ ∧
          ∃ e : X ≅ Scheme.AssociatedVectorBundle.zeroSchemeOver X ℒ P σ,
            e.hom.left ≫
                @Scheme.zeroSchemeι
                  (Scheme.AssociatedVectorBundle.totalOver X ℒ P).left _
                  (Scheme.AssociatedVectorBundle.inverseLine X ℒ P)
                  (Scheme.Modules.Invertible.tensorRight_isEquivalence
                    (Scheme.AssociatedVectorBundle.inverseLine_invertible X ℒ P)) σ =
              Scheme.AssociatedVectorBundle.zeroSection X ℒ P)

/- Lemma 42.32.4 (2): proper pushforward along the zero section preserves degree. -/
@[stacks 0F96] #check
  (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.pushforward :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [Scheme.IsRelativeSpectrumOver P] (k : ℤ),
      RelativeChow δ X k →+
        @RelativeChow S inferInstance δ inferInstance
          (Scheme.AssociatedVectorBundle.totalOver X ℒ P)
          (Scheme.AssociatedVectorBundle.totalOver_locallyOfFiniteType X ℒ P) k)

/- Lemma 42.32.4 (3): the zero section has a Cartier--Gysin pullback from degree `k + 1`
on the total space to degree `k` on the base. -/
@[stacks 0F96] #check
  (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.pullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [Scheme.IsRelativeSpectrumOver P]
      (σ : (Scheme.AssociatedVectorBundle.inverseLine X ℒ P).sections)
      (h_regular : RingedSpace.IsRegularSection
        (Scheme.AssociatedVectorBundle.inverseLine X ℒ P) σ)
      (e : X ≅ Scheme.AssociatedVectorBundle.zeroSchemeOver X ℒ P σ)
      (h_e : e.hom.left ≫
          @Scheme.zeroSchemeι
            (Scheme.AssociatedVectorBundle.totalOver X ℒ P).left _
            (Scheme.AssociatedVectorBundle.inverseLine X ℒ P)
            (Scheme.Modules.Invertible.tensorRight_isEquivalence
              (Scheme.AssociatedVectorBundle.inverseLine_invertible X ℒ P)) σ =
        Scheme.AssociatedVectorBundle.zeroSection X ℒ P) (k : ℤ),
      @RelativeChow S inferInstance δ inferInstance
          (Scheme.AssociatedVectorBundle.totalOver X ℒ P)
          (Scheme.AssociatedVectorBundle.totalOver_locallyOfFiniteType X ℒ P) (k + 1) →+
        RelativeChow δ X k)

/- Lemma 42.32.4 (4): Gysin pullback along the zero section is a left inverse to flat
pullback along the associated line-bundle projection. -/
@[stacks 0F96] #check
  (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.pullback_comp_flatPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [Scheme.IsRelativeSpectrumOver P]
      (σ : (Scheme.AssociatedVectorBundle.inverseLine X ℒ P).sections)
      (h_regular : RingedSpace.IsRegularSection
        (Scheme.AssociatedVectorBundle.inverseLine X ℒ P) σ)
      (e : X ≅ Scheme.AssociatedVectorBundle.zeroSchemeOver X ℒ P σ)
      (h_e : e.hom.left ≫
          @Scheme.zeroSchemeι
            (Scheme.AssociatedVectorBundle.totalOver X ℒ P).left _
            (Scheme.AssociatedVectorBundle.inverseLine X ℒ P)
            (Scheme.Modules.Invertible.tensorRight_isEquivalence
              (Scheme.AssociatedVectorBundle.inverseLine_invertible X ℒ P)) σ =
        Scheme.AssociatedVectorBundle.zeroSection X ℒ P) (k : ℤ),
      (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.pullback
          δ X ℒ P σ h_regular e h_e k).comp
          (@ChowGroup.flatPullback S inferInstance δ inferInstance
            (Scheme.AssociatedVectorBundle.totalOver X ℒ P) X
            (Scheme.AssociatedVectorBundle.totalOver_locallyOfFiniteType X ℒ P)
            inferInstance (Scheme.AssociatedVectorBundle.projection X ℒ P) 1
            (Scheme.AssociatedVectorBundle.projection_flat X ℒ P)
            (Scheme.AssociatedVectorBundle.projection_relativeDimension X ℒ P) k) =
        AddMonoidHom.id (RelativeChow δ X k))

/- Lemma 42.32.4 (5): zero-section pushforward is the negative of flat pullback after
capping with the first Chern class of `ℒ`. -/
@[stacks 0F96] #check
  (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.pushforward_eq_neg_firstChernClassCapThenPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [Scheme.IsRelativeSpectrumOver P] (k : ℤ),
      AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.pushforward δ X ℒ P k =
        -AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.firstChernClassCapThenPullback
          δ X ℒ P k)

/- Lemma 42.32.4 (6): the self-intersection of the zero section is capping with the
negative first Chern class of `ℒ`. -/
@[stacks 0F96] #check
  (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.gysinAt_comp_pushforward :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X : Over S) [LocallyOfFiniteType X.hom]
      (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [Scheme.IsRelativeSpectrumOver P]
      (σ : (Scheme.AssociatedVectorBundle.inverseLine X ℒ P).sections)
      (h_regular : RingedSpace.IsRegularSection
        (Scheme.AssociatedVectorBundle.inverseLine X ℒ P) σ)
      (e : X ≅ Scheme.AssociatedVectorBundle.zeroSchemeOver X ℒ P σ)
      (h_e : e.hom.left ≫
          @Scheme.zeroSchemeι
            (Scheme.AssociatedVectorBundle.totalOver X ℒ P).left _
            (Scheme.AssociatedVectorBundle.inverseLine X ℒ P)
            (Scheme.Modules.Invertible.tensorRight_isEquivalence
              (Scheme.AssociatedVectorBundle.inverseLine_invertible X ℒ P)) σ =
        Scheme.AssociatedVectorBundle.zeroSection X ℒ P) (k : ℤ),
      (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.gysinAt
          δ X ℒ P σ h_regular e h_e k).comp
          (AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.pushforward δ X ℒ P k) =
        -ChowGroup.firstChernClassCap δ X ℒ k)
