module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap64.Theorem_64_3_9_GeometricCohomology
public import stacks_project.Chap64.Theorem_64_3_9_GaloisAction
public import stacks_project.Chap64.Theorem_64_3_9_Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Geometric Frobenius pullback `π_X^*` is an isomorphism of geometric étale
cohomology, with inverse the Galois action of arithmetic Frobenius. -/
instance instIsIso_geometricFrobeniusEtaleHq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    IsIso (geometricFrobeniusEtaleHq X F j) :=
  ⟨galoisEtaleHq X F j arithmeticFrobeniusEquiv, sorry⟩

/-- Theorem 64.3.9. Let `F` be an abelian sheaf on `X.smallEtaleTopology`. Then
for all `j : ℕ`, arithmetic Frobenius `arithmeticFrobeniusEquiv` acts on
`geometricEtaleHq X F j` as the inverse of `geometricFrobeniusEtaleHq X F j`. -/
@[stacks 03SV]
theorem arithmeticFrobenius_etaleHq_eq_inv_geometricFrobenius
    (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    galoisEtaleHq X F j arithmeticFrobeniusEquiv =
      CategoryTheory.inv (geometricFrobeniusEtaleHq X F j) :=
  sorry

end AlgebraicGeometry.SchemeOverField
