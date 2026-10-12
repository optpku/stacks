/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Remark_101_5_2_SpacesOver

/-!
# Relative automorphism sheaf as a 2-fibre product

For a morphism `f : X ⟶ Y` of algebraic stacks and a morphism `x : Z ⟶ X`
from an algebraic space, the relative sheaf of automorphisms of `x` is the
2-fibre product `Z ×_{x, X} I_{X/Y}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open AlgebraicGeometry.SpacesOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

/-- The relative sheaf of automorphisms `Isom_{X/Y}(x, x)`, as the 2-fibre
product of `x : Z.toGroupoids ⟶ X` against the relative-inertia forgetful
morphism. -/
def relativeAut {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} x
    (forget.{u + 1, u, u, u + 1} f)

/-- `relativeAut f x` is the 2-fibre product of `x` against `forget f`. -/
theorem relativeAut_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    relativeAut f x =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} x
        (forget.{u + 1, u, u, u + 1} f) :=
  sorry

/-- The structure morphism `Isom_{X/Y}(x, x) ⟶ Z`. -/
def fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    relativeAut f x ⟶ Z.toGroupoids :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} x
    (forget.{u + 1, u, u, u + 1} f)

/-- `fst f x` is the first 2-fibre-product projection. -/
theorem fst_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    fst f x =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} x
        (forget.{u + 1, u, u, u + 1} f) :=
  sorry

/-- The projection `Isom_{X/Y}(x, x) ⟶ I_{X/Y}`. -/
def snd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    relativeAut f x ⟶ relativeInertia f :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} x
    (forget.{u + 1, u, u, u + 1} f)

/-- `snd f x` is the second 2-fibre-product projection. -/
theorem snd_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    snd f x =
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} x
        (forget.{u + 1, u, u, u + 1} f) :=
  sorry

/-- The 2-fibre product `Z ×_X I_{X/Y}` is an algebraic stack. -/
instance instAlgebraicStack_relativeAut {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    AlgebraicStack (relativeAut f x) :=
  sorry

/-- The structure morphism `Isom_{X/Y}(x, x) ⟶ Z` is representable by algebraic
spaces and locally of finite type. -/
instance instLocallyOfFiniteType_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    Groupoids.Hom.LocallyOfFiniteType (fst f x) :=
  sorry

/-- The relative automorphism sheaf is representable by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_relativeAut
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    IsRepresentableByAlgebraicSpace (relativeAut f x) :=
  sorry

/-- The relative automorphism sheaf, as an object of `SpacesOver` of
`Z.toGroupoids`. -/
def asSpacesOver {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) : SpacesOver Z.toGroupoids :=
  SpacesOver.mk (fst f x)
    (Groupoids.Hom.LocallyOfFiniteType.relativelyRepresentable _)

/-- The domain of `asSpacesOver f x` is `relativeAut f x`. -/
theorem asSpacesOver_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    SpacesOver.left (asSpacesOver f x) = relativeAut f x :=
  sorry

/-- The structural morphism of `asSpacesOver f x` is `fst f x`. -/
theorem asSpacesOver_hom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    SpacesOver.hom (asSpacesOver f x) = fst f x :=
  sorry

/-- Packaged relative automorphisms have algebraic-stack domain, and the
structure map to `Z` is representable by algebraic spaces. -/
theorem asSpacesOver_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    AlgebraicStack (SpacesOver.left (asSpacesOver f x)) ∧
      relativelyRepresentableByAlgebraicSpaces
        (SpacesOver.hom (asSpacesOver f x)) :=
  sorry

/-- Relative automorphisms as an object of the homotopy 1-category of
algebraic-space representable morphisms to `Z`. -/
def asHomotopy {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    Bicategory.HomotopyCategory (SpacesOver Z.toGroupoids) :=
  Bicategory.HomotopyCategory.mk (asSpacesOver f x)

/-- The underlying `SpacesOver` object of `asHomotopy f x` is
`asSpacesOver f x`. -/
theorem asHomotopy_as {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (x : Z.toGroupoids ⟶ X) :
    (asHomotopy f x).as = asSpacesOver f x :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
