/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_100_6_InverseImage
public import stacks_project.Chap59.Lemma_59_100_6_Derived
import StacksCheckRecall

@[expose] public section

/-!
Lemma 59.100.6 (0DDS) compares small étale and big fppf abelian sheaf cohomology via
`a_X = π_X ∘ ε_X`.  The reusable inverse-image functors and the six source clauses are owned
by `AlgebraicGeometry.Scheme.FppfEtale`; this chapter file is a labeled check facade.
-/

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FppfEtale
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

/- Lemma 59.100.6 (1): ε_{X,*}(a_X⁻¹ F) ≅ π_X⁻¹ F. -/
@[stacks 0DDS]
#check @aInverse_unit_isIso

/- Lemma 59.100.6 (2): R^i ε_{X,*}(a_X⁻¹ F) = 0 for i > 0. -/
@[stacks 0DDS]
#check @aInverse_higherDirectImage_isZero

/- Lemma 59.100.6 (3): for finite f, a_Y⁻¹(R^i f_small,* F) ≅ R^i f_big,fppf,*(a_X⁻¹ F). -/
@[stacks 0DDS]
#check @finite_higherDirectImage

/- Lemma 59.100.6 (4): for K in D⁺(X_étale), π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K) is an isomorphism. -/
@[stacks 0DDS]
#check @derivedUnit_isIso

/- Lemma 59.100.6 (5): for finite f and K in D⁺(X_étale),
a_Y⁻¹(Rf_small,* K) ≅ Rf_big,fppf,*(a_X⁻¹ K). -/
@[stacks 0DDS]
#check @finite_derivedPushforward

/- Lemma 59.100.6 (6): for proper f and K in D⁺(X_étale) with torsion cohomology sheaves,
a_Y⁻¹(Rf_small,* K) ≅ Rf_big,fppf,*(a_X⁻¹ K). -/
@[stacks 0DDS]
#check @proper_torsion_derivedPushforward

end
