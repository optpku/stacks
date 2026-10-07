module

public import stacks_project.Chap71.Lemma_71_5_1_FittingIdeal

/-!
# Quasi-coherence and finite type of Fitting ideals

For a finitely presented module on an algebraic space, the Fitting ideal sheaf
owned by `fittingIdealSheaf` is a quasi-coherent ideal of finite type.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Fitting ideal of a finite-type quasi-coherent `𝒪_X`-module is a
quasi-coherent ideal subobject. -/
instance instIsQuasiCoherent_fittingIdealSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (i : ℕ) : (fittingIdealSheaf F i : X.Modules).IsQuasicoherent :=
  sorry

/-- The Fitting ideal of a finitely presented `𝒪_X`-module is of finite type as
an `𝒪_X`-module. -/
instance instIsFiniteType_fittingIdealSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFinitePresentation] (r : ℕ) :
    (fittingIdealSheaf F r : X.Modules).IsFiniteType :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
