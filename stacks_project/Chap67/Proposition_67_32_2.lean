module

public import stacks_project.Chap67.Proposition_67_32_2_GenericFlatness
import StacksCheckRecall

open AlgebraicGeometry AlgebraicSpace

universe u

/- Proposition 67.32.2: a quasi-separated finite-type morphism of algebraic spaces
to a reduced algebraic space and a finite-type quasicoherent module admit a dense
open subspace on which the base change is flat and of finite presentation, and the
restricted module is flat over the open and of finite presentation. -/
@[stacks 06QT] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.exists_dense_open_genericFlatness_of_reduced_quasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsReduced Y] [QuasiSeparated f] [FiniteType f] (ℱ : X.Modules)
      [ℱ.IsQuasicoherent] [ℱ.IsFiniteType],
      ∃ W : OpenSubspace Y, Dense (W.pointsSet : Set (Points Y)) ∧
        AlgebraicGeometry.AlgebraicSpace.Modules.GenericFlatnessFinitePresentationOn f ℱ W)
