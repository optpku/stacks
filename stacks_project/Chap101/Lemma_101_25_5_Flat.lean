module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Flat morphisms of algebraic stacks

Typed compatibility checks for smooth presentations and stack flatness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.IsSmoothSurjectivePresentation :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V),
    Prop)

#check (AlgebraicGeometry.AlgebraicStack.isSmoothSurjectivePresentation_iff :
  ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} (f : X ⟶ Y)
    (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V),
    IsSmoothSurjectivePresentation f a b h ↔
      Groupoids.Hom.Smooth a ∧ Groupoids.Hom.Surjective a ∧
        Groupoids.Hom.Smooth b ∧
          Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b))

#check (AlgebraicGeometry.AlgebraicStack.Flat :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicStack.flat_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Flat f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Flat h)

#check (AlgebraicGeometry.AlgebraicStack.Flat.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    Flat (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.Flat.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f],
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V),
      IsSmoothSurjectivePresentation f a b h ∧ AlgebraicSpace.Flat h)

#check (AlgebraicGeometry.AlgebraicStack.Flat.of_groupoidsHom :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Flat f],
    Flat f)

#check (AlgebraicGeometry.AlgebraicStack.Flat.iff_groupoidsHom :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f),
    Flat f ↔ Groupoids.Hom.Flat f)

#check (AlgebraicGeometry.AlgebraicStack.Flat.of_smooth_square :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f]
    {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V)
    (φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} b f)
    (ha : Groupoids.Hom.Smooth a) (hb : Groupoids.Hom.Smooth b)
    (hφ : Groupoids.Hom.Smooth φ)
    (hfst : Nonempty
      (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} b f ≅
        AlgebraicSpace.toGroupoids.map h))
    (hsnd : Nonempty
      (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} b f ≅ a)),
    AlgebraicSpace.Flat h)
