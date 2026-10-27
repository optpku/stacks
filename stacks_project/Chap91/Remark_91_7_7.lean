/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.PushoutPullback
import StacksCheckRecall

/-!
# Functoriality of square-zero f⁻¹𝒪_S-algebra extensions by pushout and pullback

In the identity-base setting of Lemma 91.7.6, the pushout of
0 ⟶ F ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 along c : g^* F ⟶ G is a square-zero
g⁻¹ f⁻¹ 𝒪_S-algebra extension 𝒪'_1 of g⁻¹ 𝒪_X by G, and the pullback of
0 ⟶ G ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0 along g^♯ is an extension 𝒪'_2. An S-morphism
Y' ⟶ X' compatible with g and c exists iff 𝒪'_1 ≅ 𝒪'_2 as such extensions,
which are classified by the identified Ext¹ groups
Ext¹_{g⁻¹ 𝒪_X}(NL, G) = Ext¹_{𝒪_Y}(L(g)^* NL, G).
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open AlgebraicGeometry.RingedSpace.NaiveCotangent.InverseImage
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S X Y : RingedSpace.{u}}
variable {f : X ⟶ S} {g : Y ⟶ X}
variable {F : X.Modules} {G : Y.Modules}

/- Remark 91.7.7 (1) Using pushout along c : g^* F ⟶ G we construct an extension
0 ⟶ G ⟶ 𝒪'_1 ⟶ g⁻¹ 𝒪_X ⟶ 0 of square-zero g⁻¹ f⁻¹ 𝒪_S-algebras. -/
@[stacks 0GQ2] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.pushoutAlong :
    (g : Y ⟶ X) → (c : (g^*).obj F ⟶ G) →
      Solution (𝟙 S) f F (zeroKernelMap f F) →
        Solution (𝟙 S) (inverseImageTo g ≫ f) (restrictToInverseImage g G)
          (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G)))

/- Remark 91.7.7 (2) Using pullback along g^♯ : g⁻¹ 𝒪_X ⟶ 𝒪_Y we construct an
extension 0 ⟶ G ⟶ 𝒪'_2 ⟶ g⁻¹ 𝒪_X ⟶ 0 of square-zero g⁻¹ f⁻¹ 𝒪_S-algebras. -/
@[stacks 0GQ2] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.pullbackAlong :
    (g : Y ⟶ X) → Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G) →
      Solution (𝟙 S) (inverseImageTo g ≫ f) (restrictToInverseImage g G)
        (zeroKernelMap (inverseImageTo g ≫ f) (restrictToInverseImage g G)))

/- Remark 91.7.7 (3) A compatible S-morphism exists exactly when the
coefficient pushout and algebra pullback are isomorphic as extensions. -/
@[stacks 0GQ2] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.exists_fittingMap_iff_isoClass :
    ∀ (c : (g^*).obj F ⟶ G)
      (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
      (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)),
      Nonempty (IdentityBaseFitting c SX SY) ↔
        isoClassMk (pushoutAlong g c SX) = isoClassMk (pullbackAlong g SY))

/- Remark 91.7.7 (4) These extensions are classified by
Ext¹_{g⁻¹ 𝒪_X}(NL_{g⁻¹ 𝒪_X / g⁻¹ f⁻¹ 𝒪_S}, G) = Ext¹_{𝒪_Y}(L(g)^* NL[f], G),
via tensor-hom adjunction, Modules Lemma 17.31.3, and derived pullback.
The pullback compatibility is represented on lifted polynomial presentations by
J/J² ⟶ K/K² ⟶ G; the commutative lifted diagram identifies this composite with
the conormal map of the pulled-back extension. -/
@[stacks 0GQ2] #check
  (AlgebraicGeometry.RingedSpace.NaiveCotangent.InverseImage.extOne_inverseImageIso :
    (f : X ⟶ S) → (g : Y ⟶ X) → (G : Y.Modules) →
      Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj NL[inverseImageTo g ≫ f],
        (DerivedCategory.Q (C := (inverseImageSpace g).Modules)).obj
          ((CochainComplex.singleFunctor (inverseImageSpace g).Modules 0).obj
            (restrictToInverseImage g G))) ≃
        Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((DerivedCategory.Q (C := X.Modules)).obj NL[f]),
          (DerivedCategory.Q (C := Y.Modules)).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)))

/- Remark 91.7.7 The class of a coefficient pushout is the image of the original extension class under derived pullback and the coefficient map. -/
@[stacks 0GQ2] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.pushoutAlong_extClass :
    ∀ (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)),
    extOne_inverseImageIso f g G
        ((extensionEquiv (inverseImageTo g ≫ f) (restrictToInverseImage g G)).symm
          (isoClassMk (pushoutAlong g c SX))) =
      extOne_map c ((extensionEquiv f F).symm (isoClassMk SX)))

/- Remark 91.7.7 The class of an algebra pullback is the image of the original extension class under the naive-cotangent comparison. -/
@[stacks 0GQ2] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.pullbackAlong_extClass :
    ∀
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)),
    extOne_inverseImageIso f g G
        ((extensionEquiv (inverseImageTo g ≫ f) (restrictToInverseImage g G)).symm
          (isoClassMk (pullbackAlong g SY))) =
      extOne_comap f g ((extensionEquiv (g ≫ f) G).symm (isoClassMk SY)))

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
