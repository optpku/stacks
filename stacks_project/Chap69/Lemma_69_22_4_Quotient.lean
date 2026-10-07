module

public import stacks_project.Chap69.Lemma_69_22_3_Application

/-!
# Ideal-power quotients of modules on algebraic spaces

The quotient sheaf `F / I^n F` is the cokernel of the product inclusion
`I^n F ⟶ F`. Successive quotients form a tower `F / I^(n+1) F ⟶ F / I^n F`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

/-- The quotient sheaf `F / I^n F`, as the cokernel of the product inclusion
`I^n F ⟶ F`. -/
def quotient (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules] (n : ℕ) : X.Modules :=
  cokernel (product I f F n).arrow

/-- The quotient sheaf is the cokernel of the corresponding product inclusion. -/
theorem quotient_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules] (n : ℕ) :
    quotient I f F n = cokernel (product I f F n).arrow :=
  sorry

/-- The canonical projection `F ⟶ F / I^n F`. -/
def quotientMap (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules] (n : ℕ) :
    F ⟶ quotient I f F n :=
  cokernel.π (product I f F n).arrow

/-- `quotientMap` is the cokernel projection of the product inclusion. -/
theorem quotientMap_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules] (n : ℕ) :
    quotientMap I f F n = cokernel.π (product I f F n).arrow :=
  sorry

/-- The product inclusions and the identity on `F` form a commuting square, so they
induce a map of cokernels `F / I^n F ⟶ F / I^m F` whenever `m ≤ n`. -/
theorem quotientTransition_square (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    {m n : ℕ} (h : m ≤ n) :
    (product I f F n).arrow ≫ 𝟙 F =
      productInclusion I f F h ≫ (product I f F m).arrow :=
  sorry

/-- The canonical transition `F / I^n F ⟶ F / I^m F` for `m ≤ n`. -/
def quotientTransition (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules] {m n : ℕ} (h : m ≤ n) :
    quotient I f F n ⟶ quotient I f F m :=
  cokernel.map (product I f F n).arrow (product I f F m).arrow
    (productInclusion I f F h) (𝟙 F) (quotientTransition_square I f F h)

/-- `quotientTransition` is the cokernel map of the product-inclusion square. -/
theorem quotientTransition_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules] {m n : ℕ} (h : m ≤ n) :
    quotientTransition I f F h =
      cokernel.map (product I f F n).arrow (product I f F m).arrow
        (productInclusion I f F h) (𝟙 F) (quotientTransition_square I f F h) :=
  sorry

/-- The successor transition `F / I^(n+1) F ⟶ F / I^n F`. -/
def quotientStep (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules] (n : ℕ) :
    quotient I f F (n + 1) ⟶ quotient I f F n :=
  quotientTransition I f F (Nat.le_succ n)

/-- `quotientStep` is the successor case of `quotientTransition`. -/
theorem quotientStep_eq (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules] (n : ℕ) :
    quotientStep I f F n = quotientTransition I f F (Nat.le_succ n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
