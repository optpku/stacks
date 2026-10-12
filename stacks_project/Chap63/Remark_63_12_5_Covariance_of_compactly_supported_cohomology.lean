/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Remark_63_12_5_Covariance_of_compactly_supported_cohomology_Comparison
public import stacks_project.Chap63.Remark_63_12_5_Covariance_of_compactly_supported_cohomology_Trace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

/- Remark 63.12.5 (Covariance of compactly supported cohomology) (1): for a
morphism `f : X ⟶ Y` of separated finite-type schemes over a field, under
one of the conditions that `f` is étale, or flat and quasi-finite, or
quasi-finite with `Y` geometrically unibranch, or quasi-finite with an
explicit weighting `w`, Section 63.5 supplies a derived trace
`Tr_{f, w, K} : f_! f⁻¹ K ⟶ K` on `D(Y_étale, Λ)`. Direct reuse of
`weightingTraceDerived` is blocked by a declaration clash of
`sheafCompose_map_liftModuleSheafHom`; `gammaCompactSupport_weightingTraceDerived`
is the clash-forced stand-in assembled from `weightingTrace`, used only to
implement the covariance maps. -/
@[stacks 0GKS]
#check gammaCompactSupport_weightingTraceDerived

/- Remark 63.12.5 (Covariance of compactly supported cohomology) (2): in the
étale or flat quasi-finite locally finitely presented cases the canonical
weighting is `fiberWeight`, which is a positive weighting by
`fiberWeight_isPositiveWeighting`. -/
@[stacks 0GKS]
#check fiberWeight_isPositiveWeighting

/- Remark 63.12.5 (Covariance of compactly supported cohomology) (3): if `Y`
is geometrically unibranch and locally Noetherian, a nonnegative weighting
exists by `exists_genericSepDegreeWeighting`. -/
@[stacks 0GKS]
#check exists_genericSepDegreeWeighting

/- Remark 63.12.5 (Covariance of compactly supported cohomology) (4): writing
`p : X ⟶ Spec k` and `q : Y ⟶ Spec k` for the structure morphisms,
`Rq_! ∘ f_! = Rp_!` by Lemma 63.9.2 together with `Rf_! = f_!` for
quasi-finite separated `f` from Lemma 63.10.3. -/
@[stacks 0GKS]
#check gammaCompactSupport_compIso

/- Remark 63.12.5 (Covariance of compactly supported cohomology) (5): the
weighting trace therefore induces a covariance morphism
`RΓ_c(X, f⁻¹ K) ⟶ RΓ_c(Y, K)` on compactly supported cohomology. -/
@[stacks 0GKS]
#check gammaCompactSupportTrace

/- Remark 63.12.5 (Covariance of compactly supported cohomology) (6): if `Λ`
is a torsion ring, this specializes to
`Tr_f : RΓ_c(X, Λ) ⟶ RΓ_c(Y, Λ)`. -/
@[stacks 0GKS]
#check gammaCompactSupportTrace_const

end
