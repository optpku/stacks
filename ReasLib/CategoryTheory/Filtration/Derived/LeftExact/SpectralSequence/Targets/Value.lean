/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.PointwiseValue
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets.Complex
public import ReasLib.CategoryTheory.Filtration.LeftExact
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise right-derived values of finite filtered complexes

The graded-piece and underlying bounded-below derived values are functors of the source filtered
complex.  Their object and map abbreviations are retained as computation-oriented views.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace GradedPiece

/-- The pointwise right-derived values of the `p`-th graded pieces, assembled into a functor.
This is the canonical owner of both `gradedPiece` and `gradedPieceMap`. -/
@[stacks 015W "functor of right-derived graded-piece values"]
noncomputable abbrev functor (T : A ⥤ₗ B) [EnoughInjectives A] (p : ℤ) :
    CochainComplex.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B :=
  FilteredObject.Finite.Plus.GradedPiece.cochain A p ⋙
    CategoryTheory.Functor.RightDerived.Bounded.pointwiseValueFunctor
      T.obj.toBoundedBelowDerived

end GradedPiece

namespace Underlying

/-- The pointwise right-derived values of the underlying complexes, assembled into a functor.
This is the canonical owner of both `underlying` and `underlyingMap`. -/
@[stacks 015W "functor of underlying right-derived values"]
noncomputable abbrev functor (T : A ⥤ₗ B) [EnoughInjectives A] :
    CochainComplex.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B :=
  FilteredObject.Finite.Plus.Forget.cochain A ⋙
    CategoryTheory.Functor.RightDerived.Bounded.pointwiseValueFunctor
      T.obj.toBoundedBelowDerived

end Underlying

/-- The bounded-below derived value of the `p`-th graded piece of a finite filtered complex. -/
@[stacks 015W "right-derived value of a finite filtered graded piece"]
noncomputable abbrev gradedPiece (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) (p : ℤ) :
    DerivedCategory.Plus B :=
  (GradedPiece.functor T p).obj K

/-- The bounded-below derived value of the complex obtained by forgetting its finite
filtration. -/
@[stacks 015W "right-derived value of an underlying finite filtered complex"]
noncomputable abbrev underlying (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    DerivedCategory.Plus B :=
  (Underlying.functor T).obj K

/-- The derived morphism on a graded piece induced by a map of bounded-below finite filtered
complexes. -/
@[stacks 015W "map on right-derived finite filtered graded pieces"]
noncomputable abbrev gradedPieceMap (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) (p : ℤ) :
    gradedPiece T K p ⟶ gradedPiece T L p :=
  (GradedPiece.functor T p).map f

/-- The derived morphism on underlying complexes induced by a map of bounded-below finite
filtered complexes. -/
@[stacks 015W "map on right-derived underlying finite filtered complexes"]
noncomputable abbrev underlyingMap (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) :
    underlying T K ⟶ underlying T L :=
  (Underlying.functor T).map f

namespace GradedPiece

/-- Object computation for the right-derived graded-piece functor. -/
@[simp, stacks 015W "right-derived graded-piece functor computation"]
theorem functor_obj (T : A ⥤ₗ B) [EnoughInjectives A]
    (p : ℤ) (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    (functor T p).obj K = gradedPiece T K p := sorry

/-- Morphism computation for the right-derived graded-piece functor. -/
@[simp, stacks 015W "right-derived graded-piece functor computation"]
theorem functor_map (T : A ⥤ₗ B) [EnoughInjectives A]
    (p : ℤ) {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) :
    (functor T p).map f = gradedPieceMap T f p := sorry

end GradedPiece

namespace Underlying

/-- Object computation for the underlying right-derived functor. -/
@[simp, stacks 015W "underlying right-derived functor computation"]
theorem functor_obj (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    (functor T).obj K = underlying T K := sorry

/-- Morphism computation for the underlying right-derived functor. -/
@[simp, stacks 015W "underlying right-derived functor computation"]
theorem functor_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) :
    (functor T).map f = underlyingMap T f := sorry

end Underlying

/-- The derived map on a graded piece induced by an identity map is the identity. -/
@[simp, stacks 015W "functoriality of the filtered right-derived spectral sequence"]
theorem gradedPieceMap_id (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) (p : ℤ) :
    gradedPieceMap T (𝟙 K) p = 𝟙 (gradedPiece T K p) := sorry

/-- Derived maps on graded pieces respect composition. -/
@[simp, reassoc, stacks 015W "functoriality of the filtered right-derived spectral sequence"]
theorem gradedPieceMap_comp (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    gradedPieceMap T (f ≫ g) p =
      gradedPieceMap T f p ≫ gradedPieceMap T g p := sorry

/-- The derived map on an underlying complex induced by an identity map is the identity. -/
@[simp, stacks 015W "functoriality of the filtered right-derived spectral sequence"]
theorem underlyingMap_id (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    underlyingMap T (𝟙 K) = 𝟙 (underlying T K) := sorry

/-- Derived maps on underlying complexes respect composition. -/
@[simp, reassoc, stacks 015W "functoriality of the filtered right-derived spectral sequence"]
theorem underlyingMap_comp (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (f : K ⟶ L) (g : L ⟶ M) :
    underlyingMap T (f ≫ g) = underlyingMap T f ≫ underlyingMap T g := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
