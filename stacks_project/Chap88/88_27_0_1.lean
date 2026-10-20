module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor
public import stacks_project.Chap88.«88_27_0_1_Completion»
import StacksCheckRecall

/-!
# The completion functor on locally finite-type morphisms isomorphic over an open
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- 88.27.0.1: completion along a closed subset sends locally of finite type
morphisms isomorphic over its open complement to rig-étale morphisms of locally
Noetherian formal algebraic spaces. -/
@[stacks 0AR5] #check (AlgebraicGeometry.AlgebraicSpace.completionFunctor :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
    (T : Closeds (Points X)), completionAlong.Source X T ⥤ completionAlong.Target X T)
