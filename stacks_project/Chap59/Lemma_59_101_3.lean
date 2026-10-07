module

import StacksCheckRecall
public import stacks_project.Chap59.Lemma_59_101_3_DerivedGamma

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

variable (A : CommRingCat.{u})
variable [HasSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
variable [HasWeakSheafify (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}]
variable [(presheafToSheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).PreservesZeroMorphisms]
variable [Abelian (fppfAffineAbelianSheaf A)]
variable [(Sheaf.Γ (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u}).Additive]
variable [CategoryWithHomology (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf (bigAffineFppfTopology (Spec A)) AddCommGrpCat.{u})]
variable [HasDerivedCategory AddCommGrpCat.{u}]

/- Lemma 59.101.3 (1): the complex of presheaves of `𝒪`-modules on `(Aff / Spec A)_fppf
given by `Spec B / Spec A ↦ M^n ⊗[A] B`. -/
@[stacks 0H0U]
#check fppfAffineTensorExtensionComplex

/-- Optional cochain-level packaging of the comparison before derivation. -/
theorem tensorExtensionComplex_fppfAffine_toGamma_quasiIso
    (M : HomologicalComplex (ModuleCat.{u} A) (up ℤ)) :
    QuasiIso (tensorExtensionComplex_fppfAffine_toGamma A M) := sorry

/-- Lemma 59.101.3 (2): the canonical map
`M ⟶ RΓ((Aff / Spec A)_fppf, F)` is a quasi-isomorphism. -/
@[stacks 0H0U]
theorem tensorExtensionComplex_fppfAffine_derivedGamma_quasiIso
    (M : HomologicalComplex (ModuleCat.{u} A) (up ℤ)) :
    IsIso (tensorExtensionComplex_fppfAffine_toDerivedGamma A M) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
