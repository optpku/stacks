module

public import stacks_project.Chap106.«106_6_8_1_Comparison»

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom
namespace Deformation

variable {S : Scheme.{u}} {U U' I I' : AlgebraicSpace S}
variable (iU : U ⟶ U') (iI : I ⟶ I') (p' : I' ⟶ U') (p : I ⟶ U)
variable (Δ' : U' ⟶ I') (Δ : U ⟶ I)
variable [IsFirstOrderThickening iU] [IsFirstOrderThickening iI]

/-- 106.6.8.1: acting on the diagonal section `Δ'` via the spaces action-sheaf lemma
yields a sheaf isomorphism
`Hom_{O_U}(Δ^* Ω_{I/U}, C_{U/U'}) ≅ Aut(ξ)`
on `U_spaces,étale`, sending the zero section to `Δ'`. Here `Aut(ξ)` is identified
with the deformation sheaf of the first-order thickenings `(U ⊂ U')` and
`(I ⊂ I')` over `(U ⊂ U')` along `𝟙 U'` and `p'`. -/
@[stacks 0CKH]
theorem parameter_iso_aut (hΔ : IsPullback Δ iU iI Δ')
    (hp : IsPullback p iI iU p') (hsec : Δ' ≫ p' = 𝟙 U') :
    IsIsomorphic (parameterSheafEtale iU p Δ) (autSheaf iU iI p' Δ' Δ hΔ) :=
  sorry

end Deformation
end AlgebraicGeometry.AlgebraicSpace.Hom
