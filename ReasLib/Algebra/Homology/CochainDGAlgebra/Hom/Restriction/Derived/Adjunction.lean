/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Basic
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.ChangeOfRings
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom.Derived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Extension-Restriction Adjunction

This leaf adds derived extension of scalars, the evaluation-at-one comparison, and the
extension-restriction adjunction to the foundational derived restriction functor.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace CochainDGAlgebra.Hom.Derived

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}

/-- Derived extension of scalars along `f`, implemented by derived tensor with the canonical
`(A, B)`-bimodule `{}_A B_B`. -/
@[stacks 0BYX "canonical derived extension of scalars"]
abbrev extension (f : A ⟶ B) :
    CategoryTheory.Functor (DifferentialGradedModule.Derived.Category A)
      (DifferentialGradedModule.Derived.Category B) :=
  DifferentialGradedBimodule.Tensor.derivedFunctor
    (DifferentialGradedBimodule.ChangeOfRings.extension.{u, v, 0} f)

/-- Example 22.33.6 (0BYX) (1): derived internal Hom from `{}_A B_B` is canonically
isomorphic to restriction of scalars, via evaluation at `1 ∈ B`. -/
@[stacks 0BYX "derived evaluation at one"]
noncomputable def internalHomIsoRestriction (f : A ⟶ B) :
    DifferentialGradedBimodule.InternalHom.derivedFunctor
        (DifferentialGradedBimodule.ChangeOfRings.extension.{u, v, 0} f) ≅
      restriction f :=
  CategoryTheory.Functor.RightDerived.totalIsoLiftOfIso
    (F := DifferentialGradedBimodule.InternalHom.derivedSourceFunctor
      (DifferentialGradedBimodule.ChangeOfRings.extension.{u, v, 0} f))
    (G := f.restrictDgFunctor.mapK ⋙ DifferentialGradedModule.Derived.Q A)
    (L := DifferentialGradedModule.Derived.Q B)
    (DifferentialGradedModule.quasiIso B) (restriction_inverts f)
    (Functor.isoWhiskerRight
      (DifferentialGradedBimodule.ChangeOfRings.evalOneMapKIso f)
      (DifferentialGradedModule.Derived.Q A))

/-- Example 22.33.6 (0BYX) (2): derived extension of scalars is left adjoint to derived
restriction of scalars. -/
@[stacks 0BYX "derived extension-restriction adjunction"]
noncomputable def adjunction (f : A ⟶ B) : extension f ⊣ restriction f :=
  (DifferentialGradedBimodule.TensorHom.derivedAdjunction
    (DifferentialGradedBimodule.ChangeOfRings.extension.{u, v, 0} f)).ofNatIsoRight
      (internalHomIsoRestriction f)

/-- Derived restriction inherits the canonical shift comparison of the right adjoint in the
extension--restriction adjunction. -/
@[stacks 0BYX "derived restriction shift compatibility"]
noncomputable instance restrictionCommShift (f : A ⟶ B) :
    (restriction f).CommShift ℤ :=
  (adjunction f).rightAdjointCommShift ℤ

/-- Derived restriction is triangulated by the right-adjoint exactness theorem. -/
@[stacks 0BYX "derived restriction triangulated structure"]
instance restrictionIsTriangulated (f : A ⟶ B) :
    (restriction f).IsTriangulated := sorry

/-- Example 22.33.6 (0BYX) (3): the extension-restriction adjunction as a reusable Hom
equivalence. -/
@[stacks 0BYX "derived extension-restriction Hom equivalence"]
noncomputable def homEquiv (f : A ⟶ B)
    (M : DifferentialGradedModule.Derived.Category A)
    (N : DifferentialGradedModule.Derived.Category B) :
    ((extension f).obj M ⟶ N) ≃ (M ⟶ (restriction f).obj N) :=
  (adjunction f).homEquiv M N

/-- Example 22.33.6 (0BYX) (4): derived restriction is canonically derived tensor with the
regular `(B, A)`-bimodule `{}_B B_A`. -/
@[stacks 0BYX "derived restriction as tensoring with the regular bimodule"]
noncomputable def restrictionIsoTensor (f : A ⟶ B) :
    restriction f ≅
      DifferentialGradedBimodule.Tensor.derivedFunctor
        (DifferentialGradedBimodule.ChangeOfRings.restriction.{u, v, 0} f) :=
  CategoryTheory.Functor.LeftDerived.liftIsoTotalOfIso
    (F := f.restrictDgFunctor.mapK ⋙ DifferentialGradedModule.Derived.Q A)
    (G := DifferentialGradedBimodule.Tensor.derivedSourceFunctor
      (DifferentialGradedBimodule.ChangeOfRings.restriction.{u, v, 0} f))
    (L := DifferentialGradedModule.Derived.Q B)
    (DifferentialGradedModule.quasiIso B) (restriction_inverts f)
    (Functor.isoWhiskerRight
      (DifferentialGradedBimodule.ChangeOfRings.restrictionTensorMapKIso f).symm
      (DifferentialGradedModule.Derived.Q A))

end CochainDGAlgebra.Hom.Derived
