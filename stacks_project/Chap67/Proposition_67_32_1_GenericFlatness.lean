module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GenericFlatness

/-!
# Generic flatness for algebraic spaces, reduced case

This module checks the simultaneous generic-flatness conditions for a morphism of
algebraic spaces and a module sheaf, together with the existence theorem over a
reduced base.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

#check (AlgebraicGeometry.AlgebraicSpace.Modules.GenericFlatnessOn :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → X.Modules → OpenSubspace Y → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.genericFlatnessOn_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
    (W : OpenSubspace Y),
    GenericFlatnessOn f ℱ W ↔
      Flat (Limits.pullback.snd f W.ι) ∧
        LocallyOfFinitePresentation (Limits.pullback.snd f W.ι) ∧
        QuasiCompact (Limits.pullback.snd f W.ι) ∧
        flatOver ((pullback (Limits.pullback.fst f W.ι)).obj ℱ)
          (Limits.pullback.snd f W.ι) ∧
        ((pullback (Limits.pullback.fst f W.ι)).obj ℱ).IsFinitePresentation)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_dense_open_genericFlatness_of_reduced :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsReduced Y] [FiniteType f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType],
    ∃ W : OpenSubspace Y,
      Dense (W.pointsSet : Set (Points Y)) ∧ GenericFlatnessOn f ℱ W)

end AlgebraicGeometry.AlgebraicSpace.Modules
