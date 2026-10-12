/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap99.Lemma_99_12_1_Graph
public import stacks_project.Chap108.Remark_108_7_6_Numerical_invariants_Locus

/-!
# Numerical loci of relative morphisms

The numerical relative-Hom functor `Mor^P_B(Y, X)` is the preimage of
`Hilb^P_{Y ×_B X/B}` along the graph comparison `Mor_B(Y, X) ⟶ Hilb_{Y ×_B X/B}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- The structure morphism `(Y ×_B X) ⟶ B` is of finite presentation when
`Y ⟶ B` and `X ⟶ B` are. -/
instance instFinitePresentation_productHom (y : Y ⟶ B) (x : X ⟶ B)
    [FinitePresentation y] [FinitePresentation x] :
    FinitePresentation (productHom y x) :=
  sorry

/-- The structure morphism `(Y ×_B X) ⟶ B` is separated when `Y ⟶ B` and
`X ⟶ B` are. -/
instance instSeparated_productHom (y : Y ⟶ B) (x : X ⟶ B)
    [Separated y] [Separated x] :
    Separated (productHom y x) :=
  sorry

/-- The graph comparison `Mor_B(Y, X) ⟶ Hilb_{Y ×_B X/B}` at the Grothendieck
Hilbert layer. -/
def graphToHilbert (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x] :
    mor y x ⟶ Hilbert.hilbert (productHom y x) :=
  graph y x ≫ hilbToHilbert y x

/-- `graphToHilbert` is the composite of `graph` with `hilbToHilbert`. -/
theorem graphToHilbert_eq (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x] :
    graphToHilbert y x = graph y x ≫ hilbToHilbert y x :=
  sorry

/-- The numerical relative-Hom functor `Mor^P_B(Y, X)`, as the preimage of
`Hilb^P_{Y ×_B X/B}` along `graphToHilbert`. -/
def morNumerical (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    Subfunctor (mor y x) :=
  (Subfunctor.range (Hilbert.hilbertNumericalι (productHom y x) E P hE)).preimage
    (graphToHilbert y x)

/-- `morNumerical` is the preimage of the numerical Hilbert locus along
`graphToHilbert`. -/
theorem morNumerical_eq (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    morNumerical y x E P hE =
      (Subfunctor.range
          (Hilbert.hilbertNumericalι (productHom y x) E P hE)).preimage
        (graphToHilbert y x) :=
  sorry

/-- A relative morphism lies in `morNumerical` if and only if its graph lies in
the numerical Hilbert locus. -/
theorem mem_morNumerical (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) {σ : (SchemesOver B)ᵒᵖ}
    (b : (mor y x).obj σ) :
    b ∈ (morNumerical y x E P hE).obj σ ↔
      (graphToHilbert y x).app σ b ∈
        Set.range ((Hilbert.hilbertNumericalι (productHom y x) E P hE).app σ) :=
  sorry

/-- The inclusion `Mor^P_B(Y, X) ⟶ Mor_B(Y, X)`. -/
def morNumericalι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    (morNumerical y x E P hE).toFunctor ⟶ mor y x :=
  (morNumerical y x E P hE).ι

/-- `morNumericalι` is the subfunctor inclusion of `morNumerical`. -/
theorem morNumericalι_eq (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    {I : Type u} (E : I → ModuleDerived (pullback y x)) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    morNumericalι y x E P hE = (morNumerical y x E P hE).ι :=
  sorry

/-- The Hilbert-polynomial functor `Mor^{P,L}_B(Y, X)` associated to an invertible
`𝒪_{Y ×_B X}`-module `L`. -/
abbrev morNumericalHilbert (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    (L : (pullback y x).Modules) [isInvertibleObject L] (P : ℤ → ℤ) :=
  morNumerical y x (Quot.invertiblePowerFamily L) (fun n ↦ P n.down)
    (Quot.isPerfect_invertiblePowerFamily L)

/-- `morNumericalHilbert` is `morNumerical` of the family `n ↦ L^{⊗ n}`. -/
theorem morNumericalHilbert_eq (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x]
    (L : (pullback y x).Modules) [isInvertibleObject L] (P : ℤ → ℤ) :
    morNumericalHilbert y x L P =
      morNumerical y x (Quot.invertiblePowerFamily L) (fun n ↦ P n.down)
        (Quot.isPerfect_invertiblePowerFamily L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
