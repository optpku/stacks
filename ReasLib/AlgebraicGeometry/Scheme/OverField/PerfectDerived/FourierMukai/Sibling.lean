module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.EssentialImage
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.Sibling
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth.Regularity

import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.SchemeOverField.PerfectDerived

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- For a field `k` and proper `k`-schemes `X`, `Y` with `X` regular, if
`F, G : PerfectDerived X ⥤ PerfectDerived Y` are `k`-linear exact functors that agree up
to isomorphism on degree-`0` objects coming from coherent `𝒪_X`-modules of support
dimension `0`, `F` is fully faithful, and `G` is a Fourier--Mukai functor with perfect
kernel on `X ×_k Y`, then some Fourier--Mukai functor with perfect kernel on `X ×_k Y`
is a sibling of `F`. -/
theorem exists_perfectFourierMukai_areSiblings
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Scheme.Regular X.left]
    (F G : PerfectDerived X ⥤ PerfectDerived Y) [F.Linear k] [G.Linear k]
    [F.CommShift ℤ] [G.CommShift ℤ]
    (hF_exact : F.HasTriangulatedStructure) (hG_exact : G.HasTriangulatedStructure)
    [F.Full] [F.Faithful]
    (h_agree : ∀ (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ],
      topologicalKrullDim (moduleSupport ℱ) = 0 →
        Nonempty (F.obj (ofCoherentModule X ℱ) ≅ G.obj (ofCoherentModule X ℱ)))
    (hG_fm : IsPerfectFourierMukai G) :
    ∃ (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace)
      (_ : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).Linear k)
      (_ : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).CommShift ℤ)
      (hF' : (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K).HasTriangulatedStructure),
      areSiblings F (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K) hF_exact hF' :=
  sorry

/-- For a field `k` and smooth proper `k`-schemes `X`, `Y`, every
`k`-linear exact fully faithful functor `F : PerfectDerived X ⥤ PerfectDerived Y`
admits a sibling Fourier--Mukai functor with a perfect kernel on `X ×_k Y`. -/
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

/-- For a field `k` and smooth proper `k`-schemes `X`, `Y`, every
`k`-linear exact equivalence `F : PerfectDerived X ⥤ PerfectDerived Y` admits a sibling
Fourier--Mukai functor whose kernel is perfect on `X ×_k Y` and which is itself
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

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
