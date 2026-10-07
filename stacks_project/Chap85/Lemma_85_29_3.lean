module

public import stacks_project.Chap85.Lemma_85_29_3_Target
import StacksCheckRecall

/-!
# Lemma 85.29.3

A groupoid scheme over `S` determines a cartesian morphism `t_•` from the Čech nerve of `s`
to the associated simplicial scheme, with the stated low-degree identifications.
-/

@[expose] public section

open AlgebraicGeometry

/- Lemma 85.29.3 (1): let `(U, R, s, t, c)` be a groupoid scheme over a scheme `S`, let `X` be
the simplicial scheme constructed in Lemma 85.29.1, and let `(R/U)_•` be the Čech nerve of
`s`. There is a cartesian morphism `t_• : (R/U)_• ⟶ X`. -/
@[stacks 07TQ]
#check GroupoidScheme.targetSimplicial

/- Lemma 85.29.3 (2): `t_•` is a cartesian morphism of simplicial schemes. -/
@[stacks 07TQ]
#check GroupoidScheme.targetSimplicial.instIsCartesian

/- Lemma 85.29.3 (3): after identifying degree `0` of `(R/U)_•` with `R` and degree `0` of `X`
with `U`, the component of `t_•` is the target map `t`. -/
@[stacks 07TQ]
#check GroupoidScheme.targetSimplicial_app_zero

/- Lemma 85.29.3 (4): after identifying degree `1` of `(R/U)_•` with `R ×_{s,U,s} R` and degree
`1` of `X` with `R`, the component of `t_•` is right division `(r₀, r₁) ↦ r₀ ∘ r₁⁻¹`. -/
@[stacks 07TQ]
#check GroupoidScheme.targetSimplicial_app_one

/- Lemma 85.29.3 (5): after identifying degree `2` of `X` with `R ×_{s,U,t} R`, the first factor
of `t_•` is `r₀ ∘ r₁⁻¹`. -/
@[stacks 07TQ]
#check GroupoidScheme.targetSimplicial_app_two_fst

/- Lemma 85.29.3 (6): after identifying degree `2` of `X` with `R ×_{s,U,t} R`, the second factor
of `t_•` is `r₁ ∘ r₂⁻¹`. -/
@[stacks 07TQ]
#check GroupoidScheme.targetSimplicial_app_two_snd
