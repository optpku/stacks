module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.Conservative

/-!
# Conservativity of derived pushforward along affine morphisms

Restricted derived pushforward on complexes with quasi-coherent cohomology
reflects isomorphisms along an affine morphism of algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward.reflectsIsomorphisms_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f],
      (pushforwardCohomologyIn f).ReflectsIsomorphisms)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward
