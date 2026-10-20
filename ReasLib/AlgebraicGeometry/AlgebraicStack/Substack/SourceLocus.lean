/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Largest open source substacks for morphism properties
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Substack

/-- An object predicate defines an open source substack with property `P` for `f`
when it is open and the restriction of `f` has `P` for every fibredness witness
of its restricted projection. -/
def HasSourceProperty {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (A : ObjectProperty X.total) : Prop :=
  IsOpen X A ∧ ∀ h : Functor.IsFibered.InGroupoids (A.ι ⋙ X.p),
    Groupoids.Hom.has P (inclusion X A h ≫ f)

/-- Having `P` on an open source substack is equivalent to openness and having
`P` on the restriction for every fibredness witness. -/
theorem hasSourceProperty_iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (A : ObjectProperty X.total) :
    HasSourceProperty P f A ↔
      IsOpen X A ∧ ∀ h : Functor.IsFibered.InGroupoids (A.ι ⋙ X.p),
        Groupoids.Hom.has P (inclusion X A h ≫ f) := Iff.rfl

/-- An object predicate is a largest open source substack with property `P`
for `f` when it is greatest among all open source substacks with that property. -/
def IsLargestSourceOpen {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (A : ObjectProperty X.total) : Prop :=
  IsGreatest (setOf (fun B : ObjectProperty X.total ↦ HasSourceProperty P f B)) A

/-- A largest open source substack has the specified property and contains every
open source substack with that property. -/
theorem isLargestSourceOpen_iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (A : ObjectProperty X.total) :
    IsLargestSourceOpen P f A ↔
      HasSourceProperty P f A ∧
        ∀ B : ObjectProperty X.total, HasSourceProperty P f B → B ≤ A := Iff.rfl

/-- Suppose `P`, `Q`, and `R` are fppf local on the target and stable under base
change, smooth morphisms have `R`, and every algebraic-space morphism with `Q`
has a largest open source with `P`, preserved by `R`-base change. Every
representable morphism of algebraic stacks with `Q` then has a largest open
source substack with `P`, whose inverse image under every representable
`R`-base change is again the largest open source with `P`. -/
theorem exists_largestSourceOpen {S : Scheme.{u}}
    (P Q R : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    [R.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [Q.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [R.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (h_smooth : (@AlgebraicSpace.Smooth S : MorphismProperty (AlgebraicSpace S)) ≤ R)
    (h_largest : ∀ {A B : AlgebraicSpace S} (φ : A ⟶ B),
      Q φ → ∃ W : OpenSubspace A,
        P (W.ι ≫ φ) ∧
          ∀ U : OpenSubspace A, P (U.ι ≫ φ) → U.pointsSet ⊆ W.pointsSet)
    (h_baseChange : ∀ {A B B' : AlgebraicSpace S} (φ : A ⟶ B) (ψ : B' ⟶ B)
      (W : OpenSubspace A),
      Q φ → R ψ →
        (P (W.ι ≫ φ) ∧
          ∀ U : OpenSubspace A, P (U.ι ≫ φ) → U.pointsSet ⊆ W.pointsSet) →
        P ((W.inverseImage (pullback.fst φ ψ)).ι ≫ pullback.snd φ ψ) ∧
          ∀ U : OpenSubspace (pullback φ ψ),
            P (U.ι ≫ pullback.snd φ ψ) →
              U.pointsSet ⊆ (W.inverseImage (pullback.fst φ ψ)).pointsSet)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) (hQ : Groupoids.Hom.has Q f) :
    ∃ A : ObjectProperty X.total, IsLargestSourceOpen P f A ∧
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] (g : Z ⟶ Y),
        relativelyRepresentableByAlgebraicSpaces g → Groupoids.Hom.has R g →
          IsLargestSourceOpen P (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
            (fun z ↦ A ((toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g)).obj z)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Substack
