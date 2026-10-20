module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GUnramified.FinitePresentation
import StacksCheckRecall

/-!
# G-unramified morphisms of algebraic spaces versus unramified morphisms
locally of finite presentation

A morphism of algebraic spaces is G-unramified if and only if it is unramified
and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.38.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is G-unramified if and only if `f` is
unramified and locally of finite presentation. -/
@[stacks 04G1] #check
  (AlgebraicGeometry.AlgebraicSpace.gUnramified_iff_unramified_and_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      GUnramified f ↔ Unramified f ∧ LocallyOfFinitePresentation f)

#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_gUnramified :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [GUnramified f],
    LocallyOfFinitePresentation f)

#check
  (AlgebraicGeometry.AlgebraicSpace.gUnramified_of_unramified_of_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Unramified f]
      [LocallyOfFinitePresentation f], GUnramified f)

end AlgebraicGeometry.AlgebraicSpace
