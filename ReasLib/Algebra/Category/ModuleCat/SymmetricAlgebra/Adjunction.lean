/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SymmetricAlgebra
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The symmetric-algebra adjunction

The commutative-algebra-valued symmetric-algebra functor is left adjoint to
the forgetful functor to modules.  This is the semantic source of all of its
colimit-preservation instances.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CommAlgCat.symmetricAlgebra

variable (R : Type u) [CommRing R]

/-- The universal-property equivalence for the symmetric algebra. -/
@[stacks 00DQ "symmetric algebra universal property"]
noncomputable def homEquiv
    (M : ModuleCat.{max u v} R) (A : CommAlgCat.{max u v} R) :
    ((CommAlgCat.symmetricAlgebra.{u, max u v} R).obj M ⟶ A) ≃
      (M ⟶ (CommAlgCat.forgetToModule.{u, max u v} R).obj A) where
  toFun f :=
    ModuleCat.ofHom <| f.hom.toLinearMap ∘ₗ SymmetricAlgebra.ι R M
  invFun f :=
    CommAlgCat.ofHom <| SymmetricAlgebra.lift (show M →ₗ[R] A from f.hom)
  left_inv f := by
    apply CommAlgCat.hom_ext
    apply SymmetricAlgebra.algHom_ext
    ext x
    exact SymmetricAlgebra.lift_ι_apply _ x
  right_inv f := by
    apply ModuleCat.hom_ext
    exact SymmetricAlgebra.lift_comp_ι (show M →ₗ[R] A from f.hom)

/-- The symmetric-algebra/underlying-module adjunction. -/
@[stacks 00DQ "symmetric algebra adjunction"]
noncomputable def adj :
    CommAlgCat.symmetricAlgebra.{u, max u v} R ⊣
      CommAlgCat.forgetToModule.{u, max u v} R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R
      homEquiv_naturality_left_symm := by
        intro
        sorry
      homEquiv_naturality_right := by
        intro
        sorry }

/-- The symmetric-algebra functor is a left adjoint. -/
@[stacks 00DQ "symmetric algebra is a left adjoint"]
noncomputable instance isLeftAdjoint :
    (CommAlgCat.symmetricAlgebra.{u, max u v} R).IsLeftAdjoint :=
  (adj.{u, v} R).isLeftAdjoint

end CommAlgCat.symmetricAlgebra
