module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.PropertyP
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Inverted

/-!
# Underived Models for Derived Tensor Products

If the left module underlying a differential graded bimodule has property P, tensoring by that
bimodule preserves quasi-isomorphisms. Consequently every object computes the derived tensor
product and the canonical comparison with ordinary tensoring is invertible.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]

section General

variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}

/-- If tensoring by `N` already inverts quasi-isomorphisms, its canonical total left-derived
counit is an isomorphism of functors. -/
@[stacks 09LS "derived tensor counit for a localizing source"]
theorem derivedCounit_isIso_of_inverts
    {N : DifferentialGradedBimodule.{u, w, x, y} A B}
    (hN : (DifferentialGradedModule.quasiIso.{u, v, x} A).IsInvertedBy
      (derivedSourceFunctor.{u, v, w, x, y} N)) :
    IsIso (derivedCounit.{u, v, w, x, y} N) := sorry

end General

/- The regular-cell property-P owner requires the bimodule carrier to agree with the left DGA
carrier.  The source-module carrier and the right DGA carrier remain independent. -/
section LeftCarrier

variable {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, y} R}

/-- Property P for the left `A`-module underlying `N` makes ordinary tensoring by `N` preserve
quasi-isomorphisms of right differential graded `A`-modules. -/
@[stacks 0GZ2 "property-P source preserves quasi-isomorphisms for derived tensor"]
theorem derivedSourceFunctor_isInvertedBy_of_hasLeftPropertyP
    {N : DifferentialGradedBimodule.{u, v, v, y} A B}
    (hN : HasLeftPropertyP A B N) :
    (DifferentialGradedModule.quasiIso.{u, x, v} A).IsInvertedBy
      (derivedSourceFunctor.{u, x, v, v, y} N) := sorry

/-- If the left module underlying `N` has property P, every right differential graded
`A`-module computes its derived tensor product with `N`. -/
@[stacks 0GZ2 "property-P representatives compute derived tensor at every source"]
theorem computesAt_of_hasLeftPropertyP
    {N : DifferentialGradedBimodule.{u, v, v, y} A B}
    (hN : HasLeftPropertyP A B N)
    (M : K R (DifferentialGradedModule.{u, x} A)) :
    Functor.LeftDerived.ComputesAt (derivedSourceFunctor.{u, x, v, v, y} N)
      (DifferentialGradedModule.quasiIso.{u, x, v} A) M := sorry

/-- Lemma 22.33.4 (0GZ2): if the left differential graded `A`-module underlying `N` has
property P, ordinary tensoring computes `- ⊗_Aᴸ N` on every object; equivalently, the canonical
comparison from derived tensoring to ordinary tensoring is an isomorphism of functors. -/
@[stacks 0GZ2 "property-P left factor computes derived tensor products",
  stacks 0FTK "left-good bimodules compute derived tensor products"]
theorem derivedCounit_isIso_of_hasLeftPropertyP
    {N : DifferentialGradedBimodule.{u, v, v, y} A B}
    (hN : HasLeftPropertyP A B N) :
    IsIso (derivedCounit.{u, x, v, v, y} N) := sorry

/-- The derived-to-ordinary tensor comparison is invertible at each object when the left module
underlying the tensor bimodule has property P. -/
@[stacks 0GZ2 "objectwise property-P derived tensor comparison"]
theorem derivedCounit_app_isIso_of_hasLeftPropertyP
    {N : DifferentialGradedBimodule.{u, v, v, y} A B}
    (hN : HasLeftPropertyP A B N)
    (M : K R (DifferentialGradedModule.{u, x} A)) :
    IsIso ((derivedCounit.{u, x, v, v, y} N).app M) := sorry

end LeftCarrier

end DifferentialGradedBimodule.Tensor
