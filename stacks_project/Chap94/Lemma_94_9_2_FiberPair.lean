/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Slice
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Algebraic-space fiber-pair presheaves

The source-facing pair presheaf of a 1-morphism of groupoid fibrations over
`(Sch/S)_fppf` lives on `(Over U)^op`. Transport along `Over.iteratedSliceEquiv`
compares it with the functor of points of an algebraic space over `U.left`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Hom

/-- The fiber-pair isomorphism-class presheaf of `f` at `y`, reindexed from
`(Over U)^op` to `(Over U.left)^op` along the iterated slice equivalence. -/
def fiberPairClasses.overLeft {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Over S} (y : Y.p.Fiber U) :
    (Over U.left)ᵒᵖ ⥤ Type (u + 1) :=
  U.iteratedSliceEquiv.inverse.op ⋙ fiberPairClasses f y

/-- `overLeft` is precomposition of `fiberPairClasses f y` with the opposite of
the iterated-slice inverse. -/
theorem fiberPairClasses.overLeft_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Over S} (y : Y.p.Fiber U) :
    fiberPairClasses.overLeft f y =
      U.iteratedSliceEquiv.inverse.op ⋙ fiberPairClasses f y :=
  sorry

/-- The slice fiber-class presheaf of `f` along `G`, reindexed from `(Over U)^op`
to `(Over U.left)^op` along the iterated slice equivalence. -/
def sliceFiberClasses.overLeft {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Over S} (G : GroupoidsOver.slice U ⟶ Y) :
    (Over U.left)ᵒᵖ ⥤ Type (u + 1) :=
  U.iteratedSliceEquiv.inverse.op ⋙ sliceFiberClasses f G

/-- `sliceFiberClasses.overLeft` is precomposition of `sliceFiberClasses f G`
with the opposite of the iterated-slice inverse. -/
theorem sliceFiberClasses.overLeft_eq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Over S} (G : GroupoidsOver.slice U ⟶ Y) :
    sliceFiberClasses.overLeft f G =
      U.iteratedSliceEquiv.inverse.op ⋙ sliceFiberClasses f G :=
  sorry

/-- The fiber-pair presheaf at a single target-fiber object `y` is an algebraic
space over `U`, after iterated-slice transport and universe lift. -/
def fiberPairClasses.isAlgebraicSpaceAt {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {U : Over S} (y : Y.p.Fiber U) : Prop :=
  ∃ F : AlgebraicSpace U.left,
    Nonempty
      (fiberPairClasses.overLeft f y ≅
        F.functorOfPoints ⋙ uliftFunctor.{u + 1, u})

/-- Every target-fiber object has an algebraic-space fiber-pair presheaf over
its base. This is the algebraic-space analogue of
`Hom.fiberPairClasses.representable`. -/
def fiberPairClasses.isAlgebraicSpace {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop :=
  ∀ ⦃U : Over S⦄ (y : Y.p.Fiber U), fiberPairClasses.isAlgebraicSpaceAt f y

/-- The named fiber-pair algebraic-space condition unfolds to an algebraic space
over `U.left` matching `overLeft` after universe lift, for every fiber object. -/
theorem fiberPairClasses.isAlgebraicSpace_iff {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fiberPairClasses.isAlgebraicSpace f ↔
      ∀ ⦃U : Over S⦄ (y : Y.p.Fiber U),
        ∃ F : AlgebraicSpace U.left,
          Nonempty
            (fiberPairClasses.overLeft f y ≅
              F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- Every canonical slice base change of `f` has an algebraic-space fiber-class
presheaf over the slice base. -/
def sliceFiberClasses.isAlgebraicSpace {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop :=
  ∀ ⦃U : Over S⦄ (G : GroupoidsOver.slice U ⟶ Y),
    ∃ F : AlgebraicSpace U.left,
      Nonempty
        (sliceFiberClasses.overLeft f G ≅
          F.functorOfPoints ⋙ uliftFunctor.{u + 1, u})

/-- Checking algebraic-space fiber-pair presheaves on selected fiber objects is
equivalent to checking every canonical slice morphism. -/
theorem fiberPairClasses.isAlgebraicSpace_iff_slice {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    fiberPairClasses.isAlgebraicSpace f ↔
      sliceFiberClasses.isAlgebraicSpace f :=
  sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Hom

