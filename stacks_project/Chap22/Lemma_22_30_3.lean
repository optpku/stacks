module

public import ReasLib.Algebra.Module.Bimodule.TensorHom
public import ReasLib.Algebra.Module.Graded.Bimodule.TensorHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory
open scoped ModuleCat.Algebra RelativeTensor

noncomputable section

universe u v w x y z

section Ordinary

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {M : Type x} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
variable [IsScalarTower R Aᵐᵒᵖ M]
variable {N : Type y} [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
variable [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
variable [SMulCommClass A Bᵐᵒᵖ N]
variable {P : Type z} [AddCommGroup P] [Module R P] [Module Bᵐᵒᵖ P]
variable [IsScalarTower R Bᵐᵒᵖ P]

/- Lemma 22.30.3 (09LN), ordinary clause: maps from the relative tensor product and maps into
the internal Hom are canonically `R`-linearly equivalent. -/
@[stacks 09LN "ordinary modules"] #check
  (Module.Bimodule.TensorHom.equiv
      (R := R) (A := A) (B := B) (M := M) (N := N) (P := P) :
    ((M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) ≃ₗ[R]
      (M →ₗ[Aᵐᵒᵖ] Module.Bimodule.InternalHom B N P))

/- Evaluation on pure tensors and naturality characterize the ordinary adjunction. -/
#check @Module.Bimodule.TensorHom.equiv_apply
#check @Module.Bimodule.TensorHom.equiv_symm_apply
#check @Module.Bimodule.TensorHom.equiv_natural

end Ordinary

section Graded

open GradedModule

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ℤ → Submodule R B} [GradedAlgebra 𝒝]
variable (M : Right.{0, x, v, u} 𝒜)
variable (N : Bimodule.{0, y, w, v, u} 𝒜 𝒝)
variable (P : Right.{0, z, w, u} 𝒝)

/- Lemma 22.30.3 (09LN), graded clause: in every degree, homogeneous maps from the graded
relative tensor product and into the graded internal Hom are linearly equivalent. -/
@[stacks 09LN "graded modules"] #check
  (TensorHom.degreeEquiv M N P : ∀ k : ℤ,
    Right.HomogeneousMap (RelativeTensor.obj M N) P k ≃ₗ[R]
      Right.HomogeneousMap M (InternalHom.obj N P) k)

/- The degreewise equivalences assemble into the reusable total graded equivalence. -/
#check TensorHom.equiv M N P

/- Pure-tensor evaluation and three-variable naturality characterize the graded adjunction. -/
#check @TensorHom.curry_apply
#check @TensorHom.uncurry_tmul
#check @TensorHom.degreeEquiv_natural

end Graded

section DifferentialGraded

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (N : DifferentialGradedBimodule A B)
variable (M : DifferentialGradedModule A)
variable (P : DifferentialGradedModule B)

/- Lemma 22.30.3 (09LN), differential graded clause: relative tensor and fixed-source internal
Hom are canonically isomorphic as enriched Hom complexes. -/
@[stacks 09LN "differential graded modules"] #check
  (DifferentialGradedBimodule.TensorHom.homComplexIso N M P :
    homComplex (DifferentialGradedBimodule.Tensor.obj M N) P ≅
      homComplex M (DifferentialGradedBimodule.internalHom N P))

/- Its forward and inverse components recover the degreewise tensor-Hom equivalences. -/
#check @DifferentialGradedBimodule.TensorHom.homComplexIso_hom_f
#check @DifferentialGradedBimodule.TensorHom.homComplexIso_inv_f

end DifferentialGraded
