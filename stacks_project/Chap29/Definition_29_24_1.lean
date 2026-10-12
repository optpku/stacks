/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 29.24.1: a scheme morphism is submersive when its underlying topological map is
a quotient map, and it is universally submersive when every base change is submersive. -/
@[stacks 040H] #check (AlgebraicGeometry.submersive_iff_base_isQuotientMap :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
    AlgebraicGeometry.Submersive f ↔ Topology.IsQuotientMap f)

#check (AlgebraicGeometry.universallySubmersive_iff_universally :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
    AlgebraicGeometry.UniversallySubmersive f ↔
      ∀ ⦃X' Y' : AlgebraicGeometry.Scheme.{u}⦄
        (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y')
        (_ : CategoryTheory.IsPullback f' i₁ i₂ f),
        Topology.IsQuotientMap f')
