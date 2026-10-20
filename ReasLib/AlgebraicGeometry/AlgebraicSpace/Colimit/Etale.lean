/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CartesianSystem

/-!
# An étale-local colimit criterion for algebraic spaces

A cocone of algebraic spaces over `B` is a colimit as soon as the spaces-étale
base-change functor to cartesian systems is an equivalence and affine étale
mapping-out holds for affine schemes over affine étale base changes of `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {D : J ⥤ Over B}

/-- The composite `U ⟶ X ×_B B' ⟶ X` of a test object over a base change of the apex. -/
def testToApex (c : Cocone D) {B' : AlgebraicSpace S} (π : B' ⟶ B)
    {U : AlgebraicSpace S} (u : U ⟶ overPullbackObj π c.pt) : U ⟶ c.pt.left :=
  u ≫ overPullbackFst π c.pt

/-- The composite `U ⟶ X ×_B B' ⟶ B'` of a test object over a base change of the apex. -/
def testToBase (c : Cocone D) {B' : AlgebraicSpace S} (π : B' ⟶ B)
    {U : AlgebraicSpace S} (u : U ⟶ overPullbackObj π c.pt) : U ⟶ B' :=
  u ≫ overPullbackSnd π c.pt

/-- Affine étale mapping-out: maps from the pulled-back cocone `U_i = X_i ×_X U` to an affine
scheme `Z` over an affine étale base change `B' ⟶ B` extend uniquely along `U_i ⟶ U` to a
morphism `U ⟶ Z` over `B'`. -/
def HasAffineEtaleCoconeExtension (c : Cocone D) : Prop :=
  ∀ {B' : AlgebraicSpace S} (π : B' ⟶ B) [IsAffine B'] [Etale π]
    {T : Over S} [AlgebraicGeometry.IsAffine T.left] (z : ofOver T ⟶ B')
    {U : AlgebraicSpace S} [IsAffine U] (u : U ⟶ overPullbackObj π c.pt) [Etale u]
    (f : spacesEtalePullbackDiagram c (testToApex c π u) ⟶
      (Functor.const J).obj (ofOver T)),
    (∀ i, f.app i ≫ z =
        ((baseChangeCocone c (testToApex c π u)).ι.app i).left ≫ testToBase c π u) →
      ∃! φ : U ⟶ ofOver T,
        φ ≫ z = testToBase c π u ∧
          ∀ i, ((baseChangeCocone c (testToApex c π u)).ι.app i).left ≫ φ = f.app i

/-- Affine étale mapping-out unpacks as unique extension of a cocone `U_i ⟶ Z` over `B'` along
the legs `U_i ⟶ U`. -/
theorem hasAffineEtaleCoconeExtension_iff (c : Cocone D) :
    HasAffineEtaleCoconeExtension c ↔
      ∀ {B' : AlgebraicSpace S} (π : B' ⟶ B) [IsAffine B'] [Etale π]
        {T : Over S} [AlgebraicGeometry.IsAffine T.left] (z : ofOver T ⟶ B')
        {U : AlgebraicSpace S} [IsAffine U] (u : U ⟶ overPullbackObj π c.pt) [Etale u]
        (f : spacesEtalePullbackDiagram c (testToApex c π u) ⟶
          (Functor.const J).obj (ofOver T)),
        (∀ i, f.app i ≫ z =
            ((baseChangeCocone c (testToApex c π u)).ι.app i).left ≫
              testToBase c π u) →
          ∃! φ : U ⟶ ofOver T,
            φ ≫ z = testToBase c π u ∧
              ∀ i, ((baseChangeCocone c (testToApex c π u)).ι.app i).left ≫ φ =
                f.app i :=
  Iff.rfl

/-- Let `S` be a scheme and `B` an algebraic space over `S`. Let `D : J ⥤ Over B`
be a diagram of algebraic spaces over `B`, and let `c` be a cocone for `D` in `Over B`. If the
base-change functor `spacesEtaleSite c.pt.left → lim_i spacesEtaleSite (D.obj i).left` sending
`U` to `U_i = X_i ×_X U` is an equivalence, and if affine étale mapping-out holds for affine
schemes `Z` over affine étale morphisms `B' ⟶ B`, then `c` is a colimit in the category of all
algebraic spaces over `B`. -/
@[stacks 0GHL]
theorem isColimit_of_spacesEtalePullback (D : J ⥤ Over B) (c : Cocone D)
    (h_equiv : IsSpacesEtalePullbackEquivalence c)
    (h_affine : HasAffineEtaleCoconeExtension c) :
    Nonempty (IsColimit c) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
