module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Specializations
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Algebraicity of finite Hilbert stacks

The finite Hilbert stack of an algebraic space in positive degree is an
algebraic stack.
The relative finite Hilbert stack in positive degree is algebraic when its
source is representable by an algebraic space and the defining morphism is
representable, surjective, flat, and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom renaming Surjective → GroupoidSurjective, Flat → GroupoidFlat, LocallyOfFinitePresentation → GroupoidLocallyOfFinitePresentation
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

/-- For an algebraic space over a scheme and a positive degree `d`, the finite
Hilbert stack `H_d(X)` is an algebraic stack. -/
instance instAlgebraicStack_ofAlgebraicSpace {S : Scheme.{u}}
    (X : AlgebraicSpace S) (d : ℕ) [NeZero d] :
    AlgebraicStack (ofStack X.toGroupoids d).toGroupoids :=
  sorry

/-- For a representable, surjective, flat, locally finitely presented morphism
of stacks in groupoids whose source is representable by an algebraic space,
the relative finite Hilbert stack in positive degree is an algebraic stack. -/
@[stacks 06CI]
theorem algebraicStack_ofRelativeSpace {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (hX : IsRepresentableByAlgebraicSpace X)
    (d : ℕ) [NeZero d]
    [Groupoids.Hom.Surjective F] [Groupoids.Hom.Flat F]
    [Groupoids.Hom.LocallyOfFinitePresentation F] :
    AlgebraicStack (stack F d).toGroupoids :=
  sorry

/-- The relative finite Hilbert stack in positive degree is algebraic for a
representable, surjective, flat, locally finitely presented morphism of stacks
in groupoids with algebraic-space-representable source. -/
instance instAlgebraicStack_ofRelativeSpace {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (d : ℕ) [NeZero d]
    [Fact (IsRepresentableByAlgebraicSpace X)]
    [GroupoidSurjective F] [GroupoidFlat F]
    [GroupoidLocallyOfFinitePresentation F] :
    AlgebraicStack (stack F d).toGroupoids :=
  algebraicStack_ofRelativeSpace F Fact.out d

end AlgebraicGeometry.FiniteHilbertStack
