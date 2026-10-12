/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Cohomology
import StacksCheckRecall

/-!
# Cohomology of derived Hom

The canonical `RHom` cohomology comparison is owned by `ReasLib`; this chapter file records the
source equation without rebuilding tensor models, adjunctions, or comparison morphisms.

@stack 0A64
-/

@[expose] public section

/- Equation 15.74.0.2: degree-`n` cohomology of `RHom_R(L, M)` is naturally equivalent to
`Hom_{D(R)}(L, M[n])`. -/
@[stacks 0A64 "derived Hom cohomology"]
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.Cohomology.linearEquiv

/- The functor-level isomorphism records simultaneous naturality in both arguments. -/
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.Cohomology.iso
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.Cohomology.iso_natural_source
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.Cohomology.iso_natural_target
