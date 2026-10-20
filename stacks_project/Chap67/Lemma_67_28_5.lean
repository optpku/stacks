module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
import StacksCheckRecall

/-!
# Finite presentation morphisms of algebraic spaces are of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.28.5: A morphism of algebraic spaces which is locally of finite
presentation is locally of finite type. -/
@[stacks 0464] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_of_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [LocallyOfFinitePresentation f] → LocallyOfFiniteType f)

/- A morphism of algebraic spaces of finite presentation is
of finite type. -/
#check (AlgebraicGeometry.AlgebraicSpace.finiteType_of_finitePresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [FinitePresentation f] → FiniteType f)

end AlgebraicGeometry.AlgebraicSpace
