module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap76.Theorem_76_36_4_Stein_factorization_Noetherian_case_GeometricallyConnected

/-!
# Stein properties of relative normalization, Noetherian case

For a proper morphism of algebraic spaces to a locally Noetherian target, the
canonical map to the relative normalization is proper with connected geometric
fibres, and the structure morphism of the relative normalization is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The canonical map from the source into the relative normalization of a proper
morphism of algebraic spaces is proper. -/
instance instProper_toNormalization {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] : Proper (toNormalization f) :=
  sorry

/-- The canonical map from the source into the relative normalization of a proper
morphism of algebraic spaces to a locally Noetherian target has connected
geometric fibres. -/
instance instHasConnectedGeometricFibres_toNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [IsLocallyNoetherian Y] :
    HasConnectedGeometricFibres (toNormalization f) :=
  sorry

/-- The structure morphism from the relative normalization of a proper morphism
of algebraic spaces to a locally Noetherian target is finite. -/
instance instIsFinite_fromNormalization {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] [IsLocallyNoetherian Y] :
    IsFinite (fromNormalization f) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
