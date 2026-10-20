module

public import ReasLib.AlgebraicGeometry.CycleGroup.Pointwise

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.CycleGroup

universe u

variable {X : Scheme.{u}} (d : X → ℤ) (k : ℤ)

/- The degree-zero coefficient presentation of cycles supported on the weight-`k` locus. -/
#check (AlgebraicGeometry.CycleGroup.Pointwise.equiv d k :
  CycleGroup X d k ≃+ Pointwise.locallyFinite d k)

#check (AlgebraicGeometry.CycleGroup.Pointwise.coefficientsEquiv d k :
  ((x : {x : X // d x = k}) → ℤ) ≃+ Pointwise.Coefficients d k)

#check (AlgebraicGeometry.CycleGroup.Pointwise.mem_locallyFinite_iff :
  ∀ n : Pointwise.Coefficients d k, n ∈ Pointwise.locallyFinite d k ↔
    Pointwise.IsLocallyFinite n)

#check (AlgebraicGeometry.CycleGroup.Pointwise.equiv_apply d k :
  ∀ (α : CycleGroup X d k) (x : {x : X // d x = k}),
    (Pointwise.equiv d k α).1 x =
      MilnorK.degreeZeroMap (X.residueField x.1) (toAlgebraicCycle d k α x.1))

#check (AlgebraicGeometry.CycleGroup.Pointwise.equiv_symm_apply d k :
  ∀ (n : Pointwise.locallyFinite d k) (x : X),
    toAlgebraicCycle d k ((Pointwise.equiv d k).symm n) x =
      if h : d x = k then
        (MilnorK.degreeZeroEquiv (X.residueField x)).symm (n.1 ⟨x, h⟩)
      else 0)
