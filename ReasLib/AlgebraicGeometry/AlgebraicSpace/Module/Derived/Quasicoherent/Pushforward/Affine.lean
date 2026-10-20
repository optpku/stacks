module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Qcqs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward

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

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For an affine morphism of algebraic spaces, the K-injective right-derived
quasi-coherent pushforward and restricted ambient derived pushforward agree after
applying the canonical comparisons `DerivedCategory (QCoh _) ⥤ DerivedQCoh _`. -/
theorem pushforwardComparison_isomorphic_of_affine {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f] :
    IsIsomorphic (QCoh.Derived.pushforward f ⋙ comparison Y)
      (comparison X ⋙ pushforwardCohomologyIn f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
