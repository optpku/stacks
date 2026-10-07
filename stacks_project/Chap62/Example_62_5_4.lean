module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Example 62.5.4: Let `f : X ⟶ S` be a morphism of schemes which is locally of finite type.
Let `r ≥ 0` be an integer. Let `Z ⊂ X` be a closed subscheme. For `s ∈ S` denote `Z_s` the
inverse image of `Z` in `X_s`, or equivalently the scheme-theoretic fibre of `Z` at `s`
viewed as a closed subscheme of `X_s`. Assume `dim(Z_s) ≤ r` for all `s ∈ S`. Then we
associate to `Z` the family `[Z/X/S]_r` of `r`-cycles on fibres of `X/S` defined by
`[Z/X/S]_r = ([Z_s]_r)_{s ∈ S}`, where `[Z_s]_r` is given by Chow Homology,
Definition 42.9.2. -/
@[stacks 0H4S]
#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeFiberCycleFamily :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] →
    (Z : X.IdealSheafData) → (r : ℕ) →
    f.fiberClosedSubschemeDimensionLE Z r → f.FiberCycleFamily (r : ℤ))
