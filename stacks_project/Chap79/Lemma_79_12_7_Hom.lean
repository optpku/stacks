module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Basic

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Logic.Small.Defs
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-! # Structure morphism of the finite-part presheaf

The finite-part construction and its structure morphism are owned by the shared
finite-part module. This entry retains the chapter import surface.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.SubspacePoint :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Over S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.PointQuot :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Over S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.functor :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.functor_obj_equiv :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (T : Over S),
    (FinitePart.functor f).obj (op T) ≃ FinitePart.PointQuot f T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.hom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    FinitePart.functor f ⟶ Y.functorOfPoints)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.diagonal :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    FinitePart.functor f ⟶ pullback (FinitePart.hom f) (FinitePart.hom f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.diag :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    FinitePart.functor f ⟶ FinitePart.functor f ⨯ FinitePart.functor f)
