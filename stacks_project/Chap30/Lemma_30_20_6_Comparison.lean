/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import stacks_project.Chap30.Lemma_30_20_4_Quotient

/-!
# Comparison from cohomology to the quotient tower

The maps `H^p(X, F) ⟶ H^p(X, F / I^n F)` assemble to a morphism from
`Hom.cohomology f F p` to the inverse limit of the quotient cohomology tower.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient

variable {A : Type u} [CommRing A]
variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The canonical comparison `H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` induced by
`toQuotient`. -/
def toLimit (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) :
    Hom.cohomology f F p ⟶ limit (tower I f F p) :=
  limit.lift (tower I f F p)
    { pt := Hom.cohomology f F p
      π :=
        { app := fun n ↦ toQuotient I f F p n.unop
          naturality := fun _ _ _ ↦ sorry } }

/-- Projecting `toLimit` to stage `n` recovers `toQuotient`. -/
theorem toLimit_comp_π (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    toLimit I f F p ≫ limit.π (tower I f F p) (op n) = toQuotient I f F p n :=
  sorry

end AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient
