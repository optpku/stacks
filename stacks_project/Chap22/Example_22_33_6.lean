/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Adjunction
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (f : A ⟶ B)
variable (M : DifferentialGradedModule.Derived.Category.{u, v} A)
variable (N : DifferentialGradedModule.Derived.Category.{u, v} B)

/- Example 22.33.6 (0BYX) (1): evaluation at `1 ∈ B` identifies `RHom_B(B, -)` with
restriction along `φ : A ⟶ B`; deriving this isomorphism identifies right-derived Hom with
the concrete restriction localization lift. -/
@[stacks 0BYX] #check
  (CochainDGAlgebra.Hom.Derived.internalHomIsoRestriction f :
    DifferentialGradedBimodule.InternalHom.derivedFunctor
        (DifferentialGradedBimodule.ChangeOfRings.extension f) ≅
      CochainDGAlgebra.Hom.Derived.restriction f)

/- Example 22.33.6 (0BYX) (2): the derived functor of `- ⊗_A B` is left adjoint to
restriction of scalars. -/
@[stacks 0BYX] #check
  (CochainDGAlgebra.Hom.Derived.adjunction f :
    CochainDGAlgebra.Hom.Derived.extension f ⊣
      CochainDGAlgebra.Hom.Derived.restriction f)

/- Example 22.33.6 (0BYX) (3): the preceding adjunction gives the functorial equivalence
`Hom(M ⊗ᴸ_A B, N) ≃ Hom(M, N_A)`. -/
@[stacks 0BYX] #check
  (CochainDGAlgebra.Hom.Derived.homEquiv f M N :
    ((CochainDGAlgebra.Hom.Derived.extension f).obj M ⟶ N) ≃
      (M ⟶ (CochainDGAlgebra.Hom.Derived.restriction f).obj N))

/- Example 22.33.6 (0BYX) (4): restriction is canonically isomorphic to tensoring with the
regular `(B, A)`-bimodule, hence to `- ⊗ᴸ_B {}_B B_A`. -/
@[stacks 0BYX] #check
  (CochainDGAlgebra.Hom.Derived.restrictionIsoTensor f :
    CochainDGAlgebra.Hom.Derived.restriction f ≅
      DifferentialGradedBimodule.Tensor.derivedFunctor
        (DifferentialGradedBimodule.ChangeOfRings.restriction f))

#check @CochainDGAlgebra.Hom.Derived.extension
#check @CochainDGAlgebra.Hom.Derived.restriction
#check @DifferentialGradedBimodule.ChangeOfRings.evalOneIso
#check @DifferentialGradedBimodule.ChangeOfRings.restrictionTensorIso
