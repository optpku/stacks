module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom.Comparison
public import stacks_project.Chap101.Lemma_101_6_6_Comparison

/-!
# Isom comparison compatibility

The Isom construction and its computation and property API are supplied by
the shared mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.toSelfCospan :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {T : AlgebraicSpace S}
    (x1 x2 : T.toGroupoids ⟶ X),
      CospanTransform x1 x2
      (baseProjection.{u + 1, u, u + 1} T.toGroupoids)
      (baseProjection.{u + 1, u, u + 1} T.toGroupoids))

#check (AlgebraicGeometry.AlgebraicStack.toSelfCospan_left :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      (toSelfCospan x1 x2).left = 𝟙 T.toGroupoids)

#check (AlgebraicGeometry.AlgebraicStack.toSelfCospan_right :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      (toSelfCospan x1 x2).right = 𝟙 T.toGroupoids)

#check (AlgebraicGeometry.AlgebraicStack.toSelfCospan_base :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      (toSelfCospan x1 x2).base = baseProjection.{u + 1, u, u + 1} X)

#check (AlgebraicGeometry.AlgebraicStack.toSelfProduct :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {T : AlgebraicSpace S}
    (x1 x2 : T.toGroupoids ⟶ X),
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 ⟶ (FiberedCategoryOver.Groupoids.prod T.toGroupoids T.toGroupoids))

#check (AlgebraicGeometry.AlgebraicStack.toSelfProduct_eq :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      toSelfProduct x1 x2 = TwoFibreProduct.map (toSelfCospan x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomCospan :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      CospanTransform (diagonal.{u + 1, u, u + 1} T.toGroupoids)
      (toSelfProduct x1 x2) (diagonal.{u + 1, u, u + 1} T.toGroupoids)
      (toSelfProduct (x1 ≫ f) (x2 ≫ f)))

#check (AlgebraicGeometry.AlgebraicStack.isomCospan_left :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      (isomCospan f x1 x2).left = 𝟙 T.toGroupoids)

#check (AlgebraicGeometry.AlgebraicStack.isomCospan_right :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      (isomCospan f x1 x2).right = TwoFibreProduct.mapPostcompose x1 x2 f)

#check (AlgebraicGeometry.AlgebraicStack.isomCospan_base :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      (isomCospan f x1 x2).base = 𝟙 ((FiberedCategoryOver.Groupoids.prod T.toGroupoids T.toGroupoids)))

#check (AlgebraicGeometry.AlgebraicStack.isomApex :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {T : AlgebraicSpace S}
    (x1 x2 : T.toGroupoids ⟶ X),
      GroupoidsOver S)

#check (AlgebraicGeometry.AlgebraicStack.isomApex_spec :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      isomApex x1 x2 =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (diagonal.{u + 1, u, u + 1} T.toGroupoids) (toSelfProduct x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      isomApex x1 x2 ⟶ isomApex (x1 ≫ f) (x2 ≫ f))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_eq :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      isomComparison f x1 x2 = TwoFibreProduct.map (isomCospan f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_proper :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.Proper S) (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_quasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (isomComparison f x1 x2) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
      (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_isQuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_locallyQuasiFinite :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiDM f] {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (isomComparison f x1 x2))

#check (AlgebraicGeometry.AlgebraicStack.isomComparison_unramified :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [DM f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X),
      Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (isomComparison f x1 x2))

end AlgebraicGeometry.AlgebraicStack
