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

/-- Proposition 57.13.4: for a field `k` and smooth proper `k`-schemes `X`, `Y`, every
`k`-linear exact equivalence `F : PerfectDerived X ⥤ PerfectDerived Y` admits a sibling
Fourier--Mukai functor whose kernel lies in `D_perf(𝒪_{X ×_k Y})` and which is itself
an equivalence. -/
@[stacks 0G0D]
theorem exists_equivalence_sibling_perfectFourierMukai
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom]
    (F : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F.CommShift ℤ] [F.IsEquivalence]
    (hF_exact : F.HasTriangulatedStructure) :
    ∃ (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace)
      (_ : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).Linear k)
      (_ : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).CommShift ℤ)
      (hF' : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).HasTriangulatedStructure),
      areSiblings F (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K) hF_exact hF' ∧
        (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).IsEquivalence :=
  sorry

/-- The sibling Fourier--Mukai functor of `exists_equivalence_sibling_perfectFourierMukai`
is a perfect Fourier--Mukai functor. -/
theorem exists_equivalence_sibling_perfectFourierMukai_isPerfectFourierMukai
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom]
    (F : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F.CommShift ℤ] [F.IsEquivalence]
    (hF_exact : F.HasTriangulatedStructure) :
    ∃ (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace)
      (_ : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).Linear k)
      (_ : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).CommShift ℤ)
      (hF' : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).HasTriangulatedStructure),
      areSiblings F (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K) hF_exact hF' ∧
        (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).IsEquivalence ∧
          IsPerfectFourierMukai (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K) :=
  sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
