module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.WContractible

@[expose] public section

open AlgebraicGeometry

universe u

/- The affine w-contractibility characterization remains available through
the source-facing refinement module. -/
#check
  (IsWContractibleRing.iff_hasFiniteCoproductZariskiRefinement :
    {A : Type u} → [CommRing A] →
      IsWContractibleRing A ↔
        AlgebraicGeometry.Scheme.Proetale.HasFiniteCoproductZariskiRefinement
          (AlgebraicGeometry.Spec (.of A)))
