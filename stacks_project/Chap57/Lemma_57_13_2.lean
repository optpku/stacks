/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import stacks_project.Chap57.Lemma_57_12_6_FourierMukai
public import stacks_project.Chap57.Lemma_57_12_6_Siblings

import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- Lemma 57.13.2: for a field `k` and smooth proper `k`-schemes `X`, `Y`, every
`k`-linear exact fully faithful functor `F : PerfectDerived X ⥤ PerfectDerived Y`
admits a sibling Fourier--Mukai functor whose kernel lies in
`D_perf(𝒪_{X ×_k Y})`. -/
@[stacks 0G0B]
theorem exists_sibling_perfectFourierMukai
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom]
    (F : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F.CommShift ℤ] [F.Full] [F.Faithful]
    (hF_exact : F.HasTriangulatedStructure) :
    ∃ (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace)
      (_ : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).Linear k)
      (_ : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).CommShift ℤ)
      (hF' : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).HasTriangulatedStructure),
      areSiblings F (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K) hF_exact hF' :=
  sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
