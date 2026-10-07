module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import stacks_project.Chap57.Lemma_57_12_6_FourierMukai
public import stacks_project.Chap57.Lemma_57_13_2

import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- Theorem 57.13.3 (Orlov): for a field `k` and smooth proper `k`-schemes `X`, `Y`
with `X` projective over `k`, every `k`-linear fully faithful exact functor
`F : PerfectDerived X ⥤ PerfectDerived Y` is a Fourier–Mukai functor for some
kernel in `D_perf(𝒪_{X ×_k Y})`. -/
@[stacks 0G0C]
theorem isPerfectFourierMukai_of_fullyFaithful
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom]
    [HProjective X.hom]
    (F : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F.CommShift ℤ] [F.Full] [F.Faithful]
    (hF_exact : F.HasTriangulatedStructure) :
    IsPerfectFourierMukai F :=
  sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
