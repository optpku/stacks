/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.OverClass
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-!
# Scheme-theoretic images and dominance of morphisms of algebraic spaces

Scheme-theoretic images are least closed-immersion factorizations of morphisms,
and scheme-theoretic dominance is the universal-property form of a morphism
having the whole target as its scheme-theoretic image.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is scheme-theoretically dominant when every
closed immersion through which it factors is an isomorphism. -/
@[mk_iff]
class IsSchemeTheoreticallyDominant {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every closed immersion through which `f` factors is an isomorphism. -/
  isIso_of_factors {Z : AlgebraicSpace S} (i : Z ⟶ Y) [IsClosedImmersion i]
      (h : X ⟶ Z) (h_eq : h ≫ i = f) : IsIso i

namespace IsSchemeTheoreticallyDominant

/-- A morphism of algebraic spaces is scheme-theoretically dominant exactly when
every closed immersion through which it factors is an isomorphism. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsSchemeTheoreticallyDominant f ↔
      ∀ {Z : AlgebraicSpace S} (i : Z ⟶ Y) [IsClosedImmersion i] (h : X ⟶ Z),
        h ≫ i = f → IsIso i := sorry

/-- The identity morphism of an algebraic space is scheme-theoretically dominant. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsSchemeTheoreticallyDominant (𝟙 X) := sorry

/-- An isomorphism of algebraic spaces is scheme-theoretically dominant. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    IsSchemeTheoreticallyDominant f := sorry

end IsSchemeTheoreticallyDominant

/-- Two morphisms of algebraic spaces over `B` into a separated algebraic space
`Y ↘ B` are equal if they agree after precomposition with a scheme-theoretically
dominant morphism. -/
theorem ext_of_isSchemeTheoreticallyDominant_of_isSeparated
    {S : Scheme.{u}} {B X Y W : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] [Separated (Y ↘ B)]
    {f g : X ⟶ Y} [HomIsOver f B] [HomIsOver g B]
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι]
    (h_eq : ι ≫ f = ι ≫ g) : f = g := sorry

/-- Two morphisms over a separated target are equal when they agree on an open
subspace whose inclusion has scheme-theoretic closure equal to the target. -/
theorem ext_of_schemeTheoreticClosure_of_isSeparated
    {S : Scheme.{u}} {B X Y U : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] [Separated (Y ↘ B)]
    {f g : X ⟶ Y} [HomIsOver f B] [HomIsOver g B]
    (ι : U ⟶ X) [IsOpenImmersion ι] [IsSchemeTheoreticallyDominant ι]
    (h_eq : ι ≫ f = ι ≫ g) : f = g := sorry

/-- A closed immersion `ι : Z ⟶ Y` is a scheme-theoretic image of `f : X ⟶ Y`
through `toImage : X ⟶ Z` if `toImage ≫ ι = f` and every closed immersion
through which `f` factors admits a unique comparison from `Z`. -/
class IsSchemeTheoreticImage {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) : Prop where
  /-- The given maps factor `f` through the closed subspace `Z`. -/
  fac : toImage ≫ ι = f
  /-- The comparison `ι : Z ⟶ Y` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion ι
  /-- Any other closed-immersion factorization of `f` admits a unique lift from `Z`. -/
  exists_lift {Z' : AlgebraicSpace S} (toZ' : X ⟶ Z') (ι' : Z' ⟶ Y)
      [IsClosedImmersion ι'] (hfac : toZ' ≫ ι' = f) :
      ∃! lift : Z ⟶ Z', lift ≫ ι' = ι ∧ toImage ≫ lift = toZ'

namespace IsSchemeTheoreticImage

/-- A triple `(f, toImage, ι)` is a scheme-theoretic image factorization if and
only if it factors `f` through a closed immersion that is least among such. -/
theorem spec {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) :
    IsSchemeTheoreticImage f toImage ι ↔
      toImage ≫ ι = f ∧ IsClosedImmersion ι ∧
        ∀ {Z' : AlgebraicSpace S} (toZ' : X ⟶ Z') (ι' : Z' ⟶ Y)
          [IsClosedImmersion ι'], toZ' ≫ ι' = f →
          ∃! lift : Z ⟶ Z', lift ≫ ι' = ι ∧ toImage ≫ lift = toZ' := sorry

/-- The comparison from a scheme-theoretic image through any other closed-immersion
factorization of the same morphism is unique. -/
theorem lift {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] {Z' : AlgebraicSpace S}
    (toZ' : X ⟶ Z') (ι' : Z' ⟶ Y) [IsClosedImmersion ι']
    (hfac : toZ' ≫ ι' = f) :
    ∃! lift : Z ⟶ Z', lift ≫ ι' = ι ∧ toImage ≫ lift = toZ' := sorry

/-- A closed immersion of algebraic spaces is a scheme-theoretic image of itself. -/
instance of_isClosedImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsClosedImmersion f] :
    IsSchemeTheoreticImage f (𝟙 X) f := sorry

/-- The identity morphism of an algebraic space is a scheme-theoretic image of
itself. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsSchemeTheoreticImage (𝟙 X) (𝟙 X) (𝟙 X) := sorry

/-- An isomorphism of algebraic spaces is a scheme-theoretic image of itself via
the identity on the target. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIso f] : IsSchemeTheoreticImage f f (𝟙 Y) := sorry

/-- A commutative square of algebraic spaces induces a morphism between
scheme-theoretic images of the horizontal maps, filling both output squares. -/
theorem exists_imageMap {S : Scheme.{u}}
    {X1 X2 Y1 Y2 Z1 Z2 : AlgebraicSpace S}
    {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
    {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1} {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2}
    (sq : CommSq gX f₁ f₂ gY)
    [IsSchemeTheoreticImage f₁ toImage₁ ι₁]
    [IsSchemeTheoreticImage f₂ toImage₂ ι₂] :
    ∃ h : Z1 ⟶ Z2, CommSq h ι₁ ι₂ gY ∧ CommSq gX toImage₁ toImage₂ h := sorry

/-- The morphism of scheme-theoretic images induced by a commutative square is
unique. -/
theorem existsUnique_imageMap {S : Scheme.{u}}
    {X1 X2 Y1 Y2 Z1 Z2 : AlgebraicSpace S}
    {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
    {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1} {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2}
    (sq : CommSq gX f₁ f₂ gY)
    [IsSchemeTheoreticImage f₁ toImage₁ ι₁]
    [IsSchemeTheoreticImage f₂ toImage₂ ι₂] :
    ∃! h : Z1 ⟶ Z2, CommSq h ι₁ ι₂ gY ∧ CommSq gX toImage₁ toImage₂ h := sorry

/-- The scheme-theoretic image of `f₁` is contained in the scheme-theoretic
inverse image of the image of `f₂`. -/
theorem le_inverseImage {S : Scheme.{u}}
    {X1 X2 Y1 Y2 Z1 Z2 : AlgebraicSpace S}
    {f₁ : X1 ⟶ Y1} {f₂ : X2 ⟶ Y2} {gX : X1 ⟶ X2} {gY : Y1 ⟶ Y2}
    {toImage₁ : X1 ⟶ Z1} {ι₁ : Z1 ⟶ Y1} {toImage₂ : X2 ⟶ Z2} {ι₂ : Z2 ⟶ Y2}
    (sq : CommSq gX f₁ f₂ gY)
    [IsSchemeTheoreticImage f₁ toImage₁ ι₁]
    [IsSchemeTheoreticImage f₂ toImage₂ ι₂]
    [IsClosedImmersion ι₂] :
    ∃ k : Z1 ⟶ inverseImage gY ι₂, k ≫ inverseImageι gY ι₂ = ι₁ := sorry

/-- Every morphism of algebraic spaces over a scheme admits a scheme-theoretic
image factorization. -/
theorem exists_schemeTheoreticImage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃ (Z : AlgebraicSpace S) (toImage : X ⟶ Z) (ι : Z ⟶ Y),
      IsSchemeTheoreticImage f toImage ι := sorry

/-- There exists a least closed subspace of `Y` through which `f` factors: any
other such closed subspace admits a comparison over `Y`. -/
theorem exists_least_closedSubspace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    ∃ Z : ClosedSubspace Y,
      (∃ toZ : X ⟶ Z.X, toZ ≫ Z.ι = f) ∧
        ∀ Z' : ClosedSubspace Y, (∃ toZ' : X ⟶ Z'.X, toZ' ≫ Z'.ι = f) →
          ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι := sorry

/-- A least closed-subspace factorization of `f` is a scheme-theoretic image
factorization. Uniqueness of the comparison follows from closed immersions
being monomorphisms. -/
theorem of_isLeast_closedSubspace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (Z : ClosedSubspace Y) (toImage : X ⟶ Z.X)
    (hfac : toImage ≫ Z.ι = f)
    (hleast : ∀ Z' : ClosedSubspace Y,
      (∃ toZ' : X ⟶ Z'.X, toZ' ≫ Z'.ι = f) →
        ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι) :
    IsSchemeTheoreticImage f toImage Z.ι := sorry

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicSpace
