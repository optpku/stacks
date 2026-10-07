module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Rees.Blowup
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry

variable {A : Type u} [CommRing A] (I : Ideal A)

/- Exercise 111.27.7 (1): for the blowup algebra `R = reesAlgebra I`, the natural map
`b = ReesProj.toSpec I : Proj (ReesProj.grading I) ⟶ Spec (.of A)` restricts to a homeomorphism
`b : b⁻¹(U) ⟶ U` on `U = Spec(A) \ V(I)`. -/
@[stacks 02EC]
#check (AlgebraicGeometry.ReesProj.isHomeomorph_restrict_openAway I :
  IsHomeomorph (AlgebraicGeometry.ReesProj.toSpec I ∣_ AlgebraicGeometry.ReesProj.openAway I).base)

variable (Z : Set (Spec (.of A)))
variable {ξ : Spec (.of A)} {ξ' : Proj (ReesAlgebra.Grading.grade I)}
variable (hξ : IsGenericPoint ξ Z) (hU : ξ ∈ ReesProj.openAway I)
  (hξ' : ReesProj.toSpec I ξ' = ξ)

/- Exercise 111.27.7 (2): the strict transform of an irreducible closed subset `Z ⊆ Spec(A)`
meeting `U` is the closure in `Proj (reesAlgebra I)` of the unique point above the generic point
of `Z`, equivalently the closure of `Z ∩ U ⊂ U ⊂ Proj(R)`. -/
@[stacks 02EC]
#check (AlgebraicGeometry.ReesProj.strictTransform_eq_closure_singleton I hξ hU hξ' :
  ReesAlgebra.strictTransform I Z = closure {ξ'})
