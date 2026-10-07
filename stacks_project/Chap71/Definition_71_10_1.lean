module

public import stacks_project.Chap71.Definition_71_10_1_MeromorphicFunction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.10.1 (1): the sheaf of meromorphic functions 𝒦_X on X_étale is the
sheafification of U ↦ S_X(U)⁻¹ 𝒪_X(U). -/
@[stacks 0EN3] #check
  (meromorphicFunctionSheaf :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      Sheaf (smallEtaleTopology X) CommRingCat.{u + 1})

/- Definition 71.10.1 (2): a meromorphic function on X is a global section of 𝒦_X. -/
@[stacks 0EN3] #check
  (meromorphicFunctions :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) → CommRingCat.{u + 1})
