/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_9_2_Comparison
public import stacks_project.Chap108.Remark_108_5_9_Numerical_invariants_Locus

/-!
# Numerical loci of the Grothendieck Hilbert functor

The numerical Hilbert functor `Hilb^P_{X/B}` is `Quot^P_{𝒪_X/X/B}`, and the
morphism `Hilb^P_{X/B} ⟶ Hilb_{X/B}` is the numerical Quot inclusion transported
along `quotIso`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The numerical Hilbert functor `Hilb^P_{X/B}`, defined as
`Quot^P_{𝒪_X/X/B}` for a family of perfect objects `E i` in `D(𝒪_X)` and a
function `P : I → ℤ`. -/
abbrev hilbertNumerical (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :=
  Quot.quotNumerical f (SheafOfModules.unit (structureSheaf X)) E P hE

/-- `hilbertNumerical` is `quotNumerical` of the structure sheaf `𝒪_X`. -/
theorem hilbertNumerical_eq (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    hilbertNumerical f E P hE =
      Quot.quotNumerical f (SheafOfModules.unit (structureSheaf X)) E P hE :=
  sorry

/-- The morphism `Hilb^P_{X/B} ⟶ Hilb_{X/B}`, obtained by composing the
numerical Quot inclusion with the inverse of `quotIso`. -/
def hilbertNumericalι (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    (hilbertNumerical f E P hE).toFunctor ⟶ hilbert f :=
  Quot.quotNumericalι f (SheafOfModules.unit (structureSheaf X)) E P hE ≫
    (quotIso f).inv

/-- `hilbertNumericalι` is `quotNumericalι` postcomposed with `(quotIso f).inv`. -/
theorem hilbertNumericalι_eq (f : X ⟶ B) [FinitePresentation f] [Separated f]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    hilbertNumericalι f E P hE =
      Quot.quotNumericalι f (SheafOfModules.unit (structureSheaf X)) E P hE ≫
        (quotIso f).inv :=
  sorry

/-- Composing `hilbertNumericalι` with `quotIso` recovers the numerical Quot
inclusion `Quot^P_{𝒪_X/X/B} ⟶ Quot_{𝒪_X/X/B}`. -/
theorem hilbertNumericalι_comp_quotIso (f : X ⟶ B) [FinitePresentation f]
    [Separated f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    hilbertNumericalι f E P hE ≫ (quotIso f).hom =
      Quot.quotNumericalι f (SheafOfModules.unit (structureSheaf X)) E P hE :=
  sorry

/-- The Hilbert-polynomial functor `Hilb^{P,L}_{X/B}` associated to an invertible
`𝒪_X`-module `L`. -/
abbrev hilbertNumericalHilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ) :=
  Quot.quotNumericalHilbert f (SheafOfModules.unit (structureSheaf X)) L P

/-- `hilbertNumericalHilbert` is `hilbertNumerical` of the family `n ↦ L^{⊗ n}`. -/
theorem hilbertNumericalHilbert_eq (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ) :
    hilbertNumericalHilbert f L P =
      hilbertNumerical f (Quot.invertiblePowerFamily L)
        (fun n ↦ P n.down) (Quot.isPerfect_invertiblePowerFamily L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
