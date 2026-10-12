/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.TensorAlgebra
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Universe-general tensor-algebra adjunction

Mathlib owns `AlgCat.tensorAlgebra` and its same-universe adjunction.  This
leaf supplies the corresponding adjunction in a universe containing the
scalar ring, without defining a second tensor-algebra functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgCat.tensorAlgebra

variable (R : Type u) [CommRing R]

/-- The universal-property equivalence for Mathlib's tensor-algebra functor
in a universe containing the scalar ring. -/
@[stacks 00DQ "tensor algebra universal property"]
noncomputable def homEquiv
    (M : ModuleCat.{max u v} R) (A : AlgCat.{max u v} R) :
    ((AlgCat.tensorAlgebra.{max u v} R).obj M ⟶ A) ≃
      (M ⟶ (forget₂ (AlgCat.{max u v} R)
        (ModuleCat.{max u v} R)).obj A) where
  toFun f := ModuleCat.ofHom <|
    f.hom.toLinearMap ∘ₗ (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M)
  invFun f := AlgCat.ofHom <|
    TensorAlgebra.lift R (show M →ₗ[R] A from f.hom)
  left_inv f := by
    apply AlgCat.hom_ext
    exact TensorAlgebra.lift_comp_ι f.hom
  right_inv f := by
    apply ModuleCat.hom_ext
    exact TensorAlgebra.ι_comp_lift (show M →ₗ[R] A from f.hom)

/-- The tensor-algebra/underlying-module adjunction in a universe containing
the scalar ring. -/
@[stacks 00DQ "universe-general tensor algebra adjunction"]
noncomputable def adj :
    AlgCat.tensorAlgebra.{max u v} R ⊣
      forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R
      homEquiv_naturality_left_symm := by
        intro
        sorry
      homEquiv_naturality_right := by
        intro
        sorry }

/-- Mathlib's tensor-algebra functor is a left adjoint in a universe
containing the scalar ring. -/
@[stacks 00DQ "tensor algebra is a left adjoint"]
noncomputable instance isLeftAdjoint :
    (AlgCat.tensorAlgebra.{max u v} R).IsLeftAdjoint :=
  (adj.{u, v} R).isLeftAdjoint

end AlgCat.tensorAlgebra
