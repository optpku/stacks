/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme

/-!
# Pullback of zero schemes of invertible modules on algebraic spaces

A morphism of algebraic spaces pulls an invertible module and a global section
back to another such pair, and the resulting zero schemes form a cartesian
square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)
variable [isInvertibleObject ((Modules.pullback f).obj L)]

/-- The zero ideal of a pulled-back section is the inverse image of the original
zero ideal. -/
theorem zeroIdealSubobject_sectionsPullback :
    zeroIdealSubobject ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s) =
      (zeroScheme L s).idealSheaf.pullback f :=
  sorry

/-- A `T`-point of `Z(s')` composes with `f` to a `T`-point of `Z(s)`. -/
theorem vanishes_zeroIdealSubobject_sectionsPullback {T : (Over S)ᵒᵖ}
    {h : X'.functorOfPoints.obj T}
    (hh : vanishes (homOfPoint h)
      (zeroIdealSubobject ((Modules.pullback f).obj L)
        (Modules.sectionsPullback f L s))) :
    vanishes (homOfPoint (f.app T h)) (zeroIdealSubobject L s) :=
  sorry

/-- The canonical morphism from the zero scheme of a pulled-back section to the
original zero scheme. -/
noncomputable def zeroSchemePullbackMap :
    (zeroScheme ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s)).X ⟶
      (zeroScheme L s).X where
  app T :=
    TypeCat.ofHom fun
      (p : (subschemeFunctor
          (zeroIdealSubobject ((Modules.pullback f).obj L)
            (Modules.sectionsPullback f L s))).obj T) ↦
      (⟨f.app T p.val,
          vanishes_zeroIdealSubobject_sectionsPullback f L s p.property⟩ :
        (subschemeFunctor (zeroIdealSubobject L s)).obj T)
  naturality := sorry

/-- The canonical zero-scheme pullback map makes the base-change square commute. -/
theorem zeroSchemePullbackMap_comp :
    zeroSchemePullbackMap f L s ≫ zeroSchemeι L s =
      zeroSchemeι ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s) ≫ f :=
  sorry

/-- The square formed by the two zero-scheme immersions and the canonical
pullback map is cartesian. -/
theorem zeroSchemePullbackSquare :
    IsPullback
      (zeroSchemeι ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s))
      (zeroSchemePullbackMap f L s) f (zeroSchemeι L s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
