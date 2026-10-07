module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap76.Theorem_76_36_4_Stein_factorization_Noetherian_case_GeometricallyConnected

/-!
# Stein properties of relative normalization, general case

For a proper morphism of algebraic spaces, the canonical map to the relative
normalization has connected geometric fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The canonical map from the source into the relative normalization of a proper
morphism of algebraic spaces has connected geometric fibres. -/
instance instHasConnectedGeometricFibres_toNormalization_of_proper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] :
    HasConnectedGeometricFibres (toNormalization f) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
