module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Lemma_75_11_2_Coherator
public import stacks_project.Chap75.«75_5_1_1_Comparison»
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward

/-!
# Comparison of derived quasi-coherent pushforward along affine morphisms

For an affine morphism of algebraic spaces, the K-injective right-derived
quasi-coherent pushforward is compatible with restricted ambient derived
pushforward after the canonical comparisons `D(QCoh) ⥤ D_QCoh`.
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

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For an affine morphism of algebraic spaces, the K-injective right-derived
quasi-coherent pushforward and restricted ambient derived pushforward agree after
applying the canonical comparisons `DerivedCategory (QCoh _) ⥤ DerivedQCoh _`. -/
theorem pushforwardComparison_isomorphic_of_affine {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f] :
    IsIsomorphic (QCoh.Derived.pushforward f ⋙ comparison Y)
      (comparison X ⋙ pushforward f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
