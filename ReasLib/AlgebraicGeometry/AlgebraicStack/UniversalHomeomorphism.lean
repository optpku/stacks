/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Homeomorph
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Universal homeomorphisms of algebraic stacks

A morphism is a universal homeomorphism when every algebraic-stack base change
induces a homeomorphism on underlying point spaces. For morphisms representable
by algebraic spaces, this agrees with the scheme-slice universal-homeomorphism
property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- For every morphism of algebraic stacks `Z ⟶ Y`, the 2-fibre-product
projection `Z ×_Y X ⟶ Z` induces a homeomorphism of underlying point spaces. -/
def isHomeomorphAfterBaseChange {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
    AlgebraicStack.pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)

/-- Being a homeomorphism after every algebraic-stack base change means each chosen
2-fibre-product projection `Z ×_Y X ⟶ Z` induces a homeomorphism of underlying
point spaces. -/
theorem isHomeomorphAfterBaseChange_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    isHomeomorphAfterBaseChange f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
        AlgebraicStack.pointsIsHomeomorph
          (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces has the
scheme-slice universal-homeomorphism property if and only if every algebraic-stack
base change induces a homeomorphism on canonical point spaces. The induced map
is the point map of the second 2-fibre-product projection. -/
theorem has_universalHomeomorphism_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.UniversalHomeomorphism S) f ↔
      isHomeomorphAfterBaseChange f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is a universal homeomorphism if every
2-fibre-product base change induces a homeomorphism on underlying point
spaces. -/
@[mk_iff]
class UniversalHomeomorphism {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every 2-fibre-product base change of `f` induces a homeomorphism on
  points. -/
  homeomorph_baseChange {Z P : GroupoidsOver S} [AlgebraicStack Z]
      [AlgebraicStack P] {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
      (iso : fst ≫ f ≅ snd ≫ g) :
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → pointsIsHomeomorph snd

namespace UniversalHomeomorphism

/-- The identity morphism of an algebraic stack is a universal homeomorphism. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    UniversalHomeomorphism (𝟙 X) :=
  sorry

/-- The composition of a pair of universal homeomorphisms of algebraic stacks
is a universal homeomorphism. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversalHomeomorphism f] [UniversalHomeomorphism g] :
    UniversalHomeomorphism (f ≫ g) :=
  sorry

/-- A universal homeomorphism has 2-fibre-product base changes that induce
homeomorphisms on points. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [UniversalHomeomorphism f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g)
    (h : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) : pointsIsHomeomorph snd :=
  sorry

/-- The chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` of a universal
homeomorphism `f : X ⟶ Y` induces a homeomorphism on points, once the apex
is known to be an algebraic stack. -/
theorem twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} (g : Z ⟶ Y) [UniversalHomeomorphism f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversalHomeomorphism

/-- A universal homeomorphism of algebraic stacks induces a homeomorphism on
underlying point spaces. -/
theorem pointsIsHomeomorph_of_universalHomeomorphism {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [UniversalHomeomorphism f] : pointsIsHomeomorph f :=
  sorry

/-- A morphism of algebraic stacks is a universal homeomorphism if and only if
every 2-fibre-product base change, expressed by an `IsBilimit` square,
induces a homeomorphism on points. -/
theorem universalHomeomorphism_iff_pointsIsHomeomorph_of_isBilimit
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    UniversalHomeomorphism f ↔
      ∀ {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
        {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z}
        (iso : fst ≫ f ≅ snd ≫ g),
        (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → pointsIsHomeomorph snd :=
  sorry

/-- A morphism of algebraic stacks is a universal homeomorphism if and only if
every chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` induces a
homeomorphism on points. -/
theorem universalHomeomorphism_iff_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    UniversalHomeomorphism f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        pointsIsHomeomorph (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
