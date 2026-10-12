/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import stacks_project.Chap57.Lemma_57_12_6_Instances
public import stacks_project.Chap57.Lemma_57_8_9_Perfect
public import stacks_project.Chap57.Theorem_57_6_3_PerfectDerived

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- A functor `PerfectDerived X ⥤ PerfectDerived Y` is a Fourier--Mukai functor with
perfect kernel if it is isomorphic to the restricted Fourier--Mukai transform of some
perfect object on the fibre product `X ×_k Y`. -/
def IsPerfectFourierMukai {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsProper X.hom] [IsProper Y.hom]
    (F : PerfectDerived X ⥤ PerfectDerived Y) : Prop :=
  ∃ (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace),
    Nonempty (F ≅ Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K)

/-- A perfect Fourier--Mukai functor is isomorphic to the restricted transform of some
perfect kernel. -/
theorem IsPerfectFourierMukai.exists_kernel {k : Type u} [Field k]
    {X Y : SchemeOverField k} [IsProper X.hom] [IsProper Y.hom]
    {F : PerfectDerived X ⥤ PerfectDerived Y} (hF : IsPerfectFourierMukai F) :
    ∃ (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace),
      Nonempty (F ≅ Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K) := sorry

/-- The restricted Fourier--Mukai transform of a perfect kernel is a perfect
Fourier--Mukai functor. -/
theorem IsPerfectFourierMukai.ofKernel {k : Type u} [Field k]
    {X Y : SchemeOverField k} [IsProper X.hom] [IsProper Y.hom]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace) :
    IsPerfectFourierMukai (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K) := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
