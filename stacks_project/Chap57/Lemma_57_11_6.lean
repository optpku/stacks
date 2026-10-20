module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.FullyFaithful
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/- Lemma 57.11.6: for a field `k` and a proper regular `k`-scheme `X`, a `k`-linear exact
endofunctor `F` of `PerfectDerived X` that is isomorphic to the identity on every coherent
`𝒪_X`-module of `0`-dimensional support is fully faithful. -/
@[stacks 0G26] #check
  (AlgebraicGeometry.SchemeOverField.PerfectDerived.fullyFaithful_of_iso_on_zero_dimensional_support :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      [IsProper X.hom] [Scheme.Regular X.left]
      (F : PerfectDerived X ⥤ PerfectDerived X) [F.Linear k] [F.CommShift ℤ]
      (h_exact : F.HasTriangulatedStructure)
      (hF : ∀ ℱ : Coh X.left.toRingedSpace,
        topologicalKrullDim (moduleSupport ℱ.obj) = 0 →
          Nonempty (ofCoherentZeroDimSupport X ℱ ≅ F.obj (ofCoherentZeroDimSupport X ℱ))),
      Nonempty F.FullyFaithful)

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
