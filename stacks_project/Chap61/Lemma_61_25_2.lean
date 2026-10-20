/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtaleTopos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtaleLowerShriek
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ClosedImmersion

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X) [IsClosedImmersion i]

/- Lemma 61.25.2: the morphism of topoi `i_proétale` of a closed immersion
of affine schemes equals the morphism of topoi associated to the fully faithful
cocontinuous functor `v`. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.morphismOfTopoi_eq_ofContinuous i :
    (AffineIndEtale.baseChange i).sheafPullback (Type (u + 1))
        (affineIndEtaleTopology X) (affineIndEtaleTopology Z) ≅
      (AffineIndEtale.morphismOfTopoi i).inverseImage)

/- After restriction to affine ind-étale objects, inverse image along
`i_proétale` agrees with inverse image along `v`. -/
#check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.smallInverseImage_restrictionIso i :
    affineIndEtaleRestriction X ⋙
        (AffineIndEtale.morphismOfTopoi i).inverseImage ≅
      (smallProetalePullback i).sheafPullback (Type (u + 1))
          (topology X) (topology Z) ⋙
        affineIndEtaleRestriction Z)

/- Lemma 61.25.2 (1): inverse image of a type-valued sheaf is the sheaf
associated to the presheaf `V ↦ F(v(V))`. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.inverseImage_sheafify i :
    ∀ F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)),
      ((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
            (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj F =
        (presheafToSheaf (affineIndEtaleTopology Z) (Type (u + 1))).obj
          ((AffineIndEtale.lift i).op ⋙ F.obj))

/- Lemma 61.25.2 (2): on a weakly contractible object `V` of `Z_app`,
`i⁻¹ F(V) = F(v(V))`. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.inverseImage_obj_to_isIso i :
    ∀ (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
      (V : AffineIndEtale Z)
      [(affineIndEtaleTopology Z).IsWeaklyContractible V],
      IsIso (AffineIndEtale.inverseImage_obj_to i F V))

/- Lemma 61.25.2 (3): inverse image on sheaves of types has a left adjoint
`i^{Sh}_!`, obtained by extending `h_V ↦ h_{v(V)}` from weakly contractible
objects. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.sheafLowerShriekAdjunction i :
    AffineIndEtale.sheafLowerShriek i ⊣
      (AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X))

#check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.smallSheafLowerShriekAdjunction i :
    AffineIndEtale.smallSheafLowerShriek i ⊣
      (smallProetalePullback i).sheafPullback (Type (u + 1))
        (topology X) (topology Z))

/- Lemma 61.25.2 (4): inverse image on abelian sheaves has a left adjoint
`i_!`, obtained by extending `ℤ_V ↦ ℤ_{v(V)}` from weakly contractible
objects. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.abelianLowerShriekAdjunction i :
    AffineIndEtale.abelianLowerShriek i ⊣
      AffineIndEtale.abelianInverseImage i)

#check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.smallAbelianLowerShriekAdjunction i :
    AffineIndEtale.smallAbelianLowerShriek i ⊣
      (smallProetalePullback i).sheafPullback AddCommGrpCat.{u + 1}
        (topology X) (topology Z))

/- Lemma 61.25.2 (5): the unit `id ⟶ i⁻¹ i^{Sh}_!` is an isomorphism. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.smallSheafLowerShriek_unit_isIso i :
    IsIso (AffineIndEtale.smallSheafLowerShriekAdjunction i).unit)

/- Lemma 61.25.2 (5): the unit `id ⟶ i⁻¹ i_!` is an isomorphism. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.smallAbelianLowerShriek_unit_isIso i :
    IsIso (AffineIndEtale.smallAbelianLowerShriekAdjunction i).unit)

/- Lemma 61.25.2 (5): the counit `i⁻¹ i_* ⟶ id` is an isomorphism. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.sheafAdjunction_counit_isIso_of_isClosedImmersion i :
    IsIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
      (topology X) (topology Z)).counit)

/- Lemma 61.25.2 (6): direct image `i_*` is fully faithful. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.pushforwardFullyFaithful_of_isClosedImmersion i :
    ((smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
      (topology X) (topology Z)).FullyFaithful)

/- Lemma 61.25.2 (6): type-valued lower shriek `i^{Sh}_!` is fully faithful. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.smallSheafLowerShriekFullyFaithful i :
    (AffineIndEtale.smallSheafLowerShriek i).FullyFaithful)

/- Lemma 61.25.2 (6): abelian lower shriek `i_!` is fully faithful. -/
@[stacks 09BL] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.smallAbelianLowerShriekFullyFaithful i :
    (AffineIndEtale.smallAbelianLowerShriek i).FullyFaithful)
