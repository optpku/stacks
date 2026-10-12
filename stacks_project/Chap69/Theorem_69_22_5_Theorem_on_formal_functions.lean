/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Homeomorph.Defs
public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import stacks_project.Chap69.Theorem_69_22_5_Theorem_on_formal_functions_Comparison

/-!
# Theorem on formal functions

In Situation 69.22.1, the descended comparisons
`H^p(X, F) / I^n H^p(X, F) ⟶ H^p(X, F / I^n F)` induce an isomorphism from
the I-adic completion of `H^p(X, F)` to the inverse limit of the quotient
cohomology system, and this comparison is a homeomorphism of the two limit
topologies.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IdealPowerCohomology

/-- Theorem 69.22.5 (Theorem on formal functions) (1): in Situation 69.22.1, for
each `p : ℕ` the induced comparison from the I-adic completion of
`H^p(X, F)` to `lim_n H^p(X, F / I^n F)` is an isomorphism of `A`-modules. -/
@[stacks 08AZ]
instance isIso_limitComparison [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    IsIso (limitComparison I f F p) :=
  sorry

/-- Theorem 69.22.5 (Theorem on formal functions) (2): in Situation 69.22.1, the
same comparison is a homeomorphism between the inverse-limit topology on the
I-adic completion and the limit topology on `lim_n H^p(X, F / I^n F)`. -/
@[stacks 08AZ]
theorem isHomeomorph_limitComparison [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    @IsHomeomorph
      (AdicCompletion I
        (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))
      (limit (quotientSystem I f F p) : ModuleCat A)
      (⨅ n, TopologicalSpace.induced
        (AdicCompletion.eval I
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) n) ⊥)
      (Functor.limitTopology (quotientSystem I f F p))
      (limitComparison I f F p).hom :=
  sorry

end IdealPowerCohomology
end AlgebraicGeometry.AlgebraicSpace.Modules
