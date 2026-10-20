module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.AbsoluteAffineDiagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence

/-!
# Comparison of derived quasi-coherent pushforward on quasi-compact algebraic spaces
with affine diagonal

For a morphism of quasi-compact algebraic spaces with affine diagonal over the
terminal scheme, the K-injective right-derived quasi-coherent pushforward is
compatible with restricted ambient derived pushforward after the canonical
comparisons `D(QCoh) ⥤ D_QCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a morphism of quasi-compact algebraic spaces with affine diagonal over the
terminal scheme, the K-injective right-derived quasi-coherent pushforward and
restricted ambient derived pushforward agree after applying the canonical
comparisons `DerivedCategory (QCoh _) ⥤ DerivedQCoh _`. -/
theorem pushforwardComparison_isomorphic_of_compact_affineDiagonal {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsQuasiCompact Y]
    [IsAbsolutelyAffineDiagonal X] [IsAbsolutelyAffineDiagonal Y] :
    IsIsomorphic (QCoh.Derived.pushforward f ⋙ comparison Y)
      (comparison X ⋙ pushforwardCohomologyIn f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
