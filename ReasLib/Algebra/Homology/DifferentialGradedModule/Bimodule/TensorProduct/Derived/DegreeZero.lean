/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DegreeZero.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Tensor Functors for Ordinary Algebras

This file transports the DG-derived tensor functor for degree-zero DG algebras across the
canonical equivalences with ordinary derived categories of right modules.
-/

@[expose] public section

noncomputable section

universe u uA uB v w

open CategoryTheory
open scoped ModuleCat.Algebra

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A : Type uA} {B : Type uB} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- Derived tensoring by a DG bimodule between the degree-zero DGA models of `A` and `B`,
transported to ordinary derived categories of right modules.  The algebra carriers, source-module
carrier, and bimodule carrier may live in independent universes; the target module carrier is the
maximum of the source-module and bimodule carriers.
Allowing an arbitrary DG bimodule is essential: a tilting complex need not be concentrated in
degree zero. -/
@[stacks 09SC "derived tensor functor for ordinary algebras"]
noncomputable def ordinaryDerivedFunctor
    (N : DifferentialGradedBimodule.{u, w, uA, uB}
      (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B)) :
    DerivedCategory (ModuleCat.{v} (Aᵐᵒᵖ)) ⥤
      DerivedCategory (ModuleCat.{max v w} (Bᵐᵒᵖ)) :=
  DifferentialGradedModule.DegreeZero.toDerived.{u, uA, v} R A ⋙
    derivedFunctor.{u, v, w, uA, uB} N ⋙
    DifferentialGradedModule.DegreeZero.fromDerived.{u, uB, max v w} R B

/-- The ordinary derived tensor functor transported from the DG model is `R`-linear. -/
@[stacks 09SC "linearity of the ordinary derived tensor functor"]
instance ordinaryDerivedFunctor_linear
    (N : DifferentialGradedBimodule.{u, w, uA, uB}
      (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B)) :
    (ordinaryDerivedFunctor.{u, uA, uB, v, w} N).Linear R := sorry

/-- The transported ordinary derived tensor functor commutes with integer shifts. -/
@[stacks 09SC "shift compatibility of the ordinary derived tensor functor"]
noncomputable instance ordinaryDerivedFunctor_commShift
    (N : DifferentialGradedBimodule.{u, w, uA, uB}
      (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B)) :
    (ordinaryDerivedFunctor.{u, uA, uB, v, w} N).CommShift ℤ :=
  Functor.CommShift.comp
    (DifferentialGradedModule.DegreeZero.toDerived.{u, uA, v} R A ⋙
      derivedFunctor.{u, v, w, uA, uB} N)
    (DifferentialGradedModule.DegreeZero.fromDerived.{u, uB, max v w} R B)

/-- The transported ordinary derived tensor functor preserves distinguished triangles. -/
@[stacks 09SC "triangulated ordinary derived tensor functor"]
instance ordinaryDerivedFunctor_isTriangulated
    (N : DifferentialGradedBimodule.{u, w, uA, uB}
      (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B)) :
    (ordinaryDerivedFunctor.{u, uA, uB, v, w} N).IsTriangulated := sorry

section

variable (N : DifferentialGradedBimodule.{u, w, uA, uB}
  (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B))

#synth (ordinaryDerivedFunctor.{u, uA, uB, v, w} N).CommShift ℤ
#synth (ordinaryDerivedFunctor.{u, uA, uB, v, w} N).IsTriangulated

end

end DifferentialGradedBimodule.Tensor
