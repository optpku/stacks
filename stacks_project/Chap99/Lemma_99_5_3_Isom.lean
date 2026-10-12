/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import stacks_project.Chap99.Situation_99_5_1_Category

/-!
# Isomorphism presheaves of the stack of coherent sheaves

In Situation 99.5.1, fibrewise isomorphism presheaves of `p : Obj f ⥤ Over S`
are transported along the iterated slice equivalence to schemes over the test
scheme, then compared with functors of points of algebraic spaces after a
universe lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The isomorphism presheaf `Isom_𝒳(x, y)` of two fibre objects of `p f` over a
scheme `T` over `S`, reindexed along `T.iteratedSliceEquiv` to a presheaf on
schemes over `T.left`. Hom-types of `Obj f` live in `Type (u + 1)`. -/
def isomOverLeft {f : X ⟶ B} [FinitePresentation f] [Functor.IsFibered (p f)]
    {T : Over S} (x y : (p f).Fiber T) : (Over T.left)ᵒᵖ ⥤ Type (u + 1) :=
  T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf (p f) x y

/-- `isomOverLeft x y` is precomposition of `Functor.isomorphismPresheaf (p f) x y`
with the opposite of the iterated-slice inverse. -/
theorem isomOverLeft_eq {f : X ⟶ B} [FinitePresentation f]
    [Functor.IsFibered (p f)] {T : Over S} (x y : (p f).Fiber T) :
    isomOverLeft x y =
      T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf (p f) x y :=
  sorry

/-- The transported isomorphism presheaf at a pair of fibre objects is an
algebraic space over `T`, after universe lift of the functor of points. -/
def isAlgebraicSpaceAt {f : X ⟶ B} [FinitePresentation f]
    [Functor.IsFibered (p f)] {T : Over S} (x y : (p f).Fiber T) : Prop :=
  ∃ F : AlgebraicSpace T.left,
    Nonempty (isomOverLeft x y ≅ F.functorOfPoints ⋙ uliftFunctor.{u + 1, u})

/-- Being an algebraic space over `T` means some algebraic space over `T.left`
has functor of points isomorphic to `isomOverLeft x y` after universe lift. -/
theorem isAlgebraicSpaceAt_iff {f : X ⟶ B} [FinitePresentation f]
    [Functor.IsFibered (p f)] {T : Over S} (x y : (p f).Fiber T) :
    isAlgebraicSpaceAt x y ↔
      ∃ F : AlgebraicSpace T.left,
        Nonempty (isomOverLeft x y ≅ F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- Every pair of fibre objects of `p f` has an algebraic-space isomorphism
presheaf over its base. This is the 94.10.11(1) meaning of a representable
diagonal at Hom-universe `u + 1`. -/
def isAlgebraicSpace (f : X ⟶ B) [FinitePresentation f]
    [Functor.IsFibered (p f)] : Prop :=
  ∀ ⦃T : Over S⦄ (x y : (p f).Fiber T), isAlgebraicSpaceAt x y

/-- The global algebraic-space Isom condition unfolds to `isAlgebraicSpaceAt` at
every fibre pair. -/
theorem isAlgebraicSpace_iff (f : X ⟶ B) [FinitePresentation f]
    [Functor.IsFibered (p f)] :
    isAlgebraicSpace f ↔
      ∀ ⦃T : Over S⦄ (x y : (p f).Fiber T), isAlgebraicSpaceAt x y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
