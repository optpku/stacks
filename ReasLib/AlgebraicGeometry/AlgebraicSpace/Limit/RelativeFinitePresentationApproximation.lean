module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A diagram approximates a morphism when its cone with vertex the source is
limiting, its legs recover the morphism over the target, its transition maps
are affine, and its stage maps have finite presentation. -/
def IsRelativeFinitePresentationApproximation {S : Scheme.{u}} {I : Type u} [Preorder I]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (D : OrderDual I ⥤ AlgebraicSpace S)
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : D ⟶ (Functor.const (OrderDual I)).obj Y) : Prop :=
  Nonempty (IsLimit (Cone.mk X π)) ∧
    (∀ i, π.app i ≫ σ.app i = f) ∧
    (∀ {i j : I} (h : i ≤ j), Affine (D.map (homOfLE h))) ∧
    ∀ i, FinitePresentation (σ.app i)

/-- A relative finite-presentation approximation is precisely a limiting cone
recovering the morphism over the target, with affine transitions and
finite-presentation stage maps. -/
theorem isRelativeFinitePresentationApproximation_iff
    {S : Scheme.{u}} {I : Type u} [Preorder I] {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (D : OrderDual I ⥤ AlgebraicSpace S)
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : D ⟶ (Functor.const (OrderDual I)).obj Y) :
    IsRelativeFinitePresentationApproximation f D π σ ↔
      Nonempty (IsLimit (Cone.mk X π)) ∧
        (∀ i, π.app i ≫ σ.app i = f) ∧
        (∀ {i j : I} (h : i ≤ j), Affine (D.map (homOfLE h))) ∧
        ∀ i, FinitePresentation (σ.app i) :=
  Iff.rfl

/-- A quasi-compact, absolutely quasi-separated algebraic space mapping to an
absolutely quasi-separated algebraic space is a directed inverse limit over
the target with affine transitions and finite-presentation stages. -/
theorem exists_relativeFinitePresentationApproximation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyQuasiSeparated Y] :
    ∃ (I : Type u) (preorderI : Preorder I) (nonemptyI : Nonempty I)
      (directedI : IsDirected I (· ≤ ·)) (D : OrderDual I ⥤ AlgebraicSpace S)
      (π : (Functor.const (OrderDual I)).obj X ⟶ D)
      (σ : D ⟶ (Functor.const (OrderDual I)).obj Y),
      IsRelativeFinitePresentationApproximation f D π σ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
