module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward

/-!
# Conservativity of derived pushforward along affine morphisms

Restricted derived pushforward on complexes with quasi-coherent cohomology
reflects isomorphisms along an affine morphism of algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiCompact

/-- An affine morphism of algebraic spaces is quasi-compact. -/
instance (priority := 900) of_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Affine f] : QuasiCompact f :=
  sorry

end QuasiCompact

namespace QuasiSeparated

/-- An affine morphism of algebraic spaces is quasi-separated. -/
instance (priority := 900) of_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Affine f] : QuasiSeparated f :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward

/-- Restricted derived pushforward along an affine morphism of algebraic spaces
reflects isomorphisms. -/
instance reflectsIsomorphisms_of_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Affine f] :
    (pushforward f).ReflectsIsomorphisms :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward
