/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.Scheme.Presheaf.Fiber

/-!
# Pullback description of fibers of presheaf transformations
-/

@[expose] public section

open CategoryTheory Opposite Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over

/-- A section over a scheme determines a morphism from the constant singleton presheaf
to the restriction of the presheaf along the scheme's structure morphism. -/
def terminalSection {S : Scheme.{u}} {G : (Over S)ᵒᵖ ⥤ Type v} {T : Over S}
    (y : G.obj (op T)) :
    (Functor.const ((Over T.left)ᵒᵖ)).obj (PUnit : Type v) ⟶
      (Over.map T.hom).op ⋙ G where
  app T' := ↾fun _ ↦ restrictSection y T'.unop
  naturality := sorry

/-- The component of the terminal section at a scheme over the base evaluates at the
unique point to the restriction of the original section. -/
theorem terminalSection_app {S : Scheme.{u}} {G : (Over S)ᵒᵖ ⥤ Type v}
    {T : Over S} (y : G.obj (op T)) (T' : (Over T.left)ᵒᵖ) :
    (terminalSection y).app T' PUnit.unit = restrictSection y T'.unop :=
  sorry

/-- The fiber of a presheaf transformation is the pullback of its restriction along a
scheme with the constant singleton presheaf determined by the chosen section. -/
@[stacks 049K]
theorem fiber_isPullback {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T : Over S} (y : G.obj (op T)) :
    IsPullback (fiber a y).ι
      ((Functor.isTerminalConst _ Types.isTerminalPUnit).from (fiberFunctor a y))
      (Functor.whiskerLeft (Over.map T.hom).op a) (terminalSection y) :=
  sorry

end AlgebraicGeometry.Scheme.Over
