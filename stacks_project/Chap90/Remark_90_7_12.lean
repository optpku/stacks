/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Remark_90_7_12_Comparison
public import stacks_project.Chap90.Remark_90_7_12_Underline
import StacksCheckRecall

@[expose] public section

open CategoryTheory FormalObject
open scoped BasedFunctor

/- Remark 90.7.12 (1): for `R` in `Ĉ_Λ` and `F` cofibered in groupoids over `C_Λ`,
evaluation of a based morphism `φ : underline R |_{C_Λ} ⟶ F` on the identity
truncations `R ⟶ R ⧸ m_R^{n+1}` yields an equivalence
`Mor_{C_Λ}(underline R |_{C_Λ}, F) ⥤ hat F(R)`. -/
@[stacks 06HC] #check FormalObject.fromRestrictedHom

/- Remark 90.7.12 (2): the equivalence is the composite of `Φ` from Remark 90.7.9,
specialized to `underline R`, with cofibered 2-Yoneda evaluation at `𝟙 R`. -/
@[stacks 06HC] #check FormalObject.fromRestrictedHom_comp_phi

/- Remark 90.7.12 (3): given a choice of pushforwards for `F`, a formal object `ξ`
over `R` determines an explicit quasi-inverse `underline ξ` sending `α : R ⟶ A` to
`α_{m,*} ξ_m`, where `m = nilpotencyIndex A`. -/
@[stacks 06HC] #check FormalObject.toRestrictedHom

/- Remark 90.7.12 (4): given a choice of pushforwards for `hat F`, cofibered 2-Yoneda
supplies the quasi-inverse `ι` sending `ξ` to the based morphism `f ↦ f_* ξ`. -/
@[stacks 06HC] #check FormalObject.iota

/- Remark 90.7.12 (5): `Ψ(ι ξ) ≅ underline ξ` as based morphisms over `C_Λ`. -/
@[stacks 06HC] #check FormalObject.homEquivInverse_iota_iso

/- Remark 90.7.12 (6): `ι ξ` is isomorphic to the completion of `underline ξ`. -/
@[stacks 06HC] #check FormalObject.iota_iso_completion
