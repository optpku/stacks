/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_AdicStarRing
public import stacks_project.Chap88.«88_3_0_1»
public import stacks_project.Chap88.Remark_88_11_2_Presentation
public import stacks_project.Chap88.Remark_88_11_2_Comparison

/-!
# Remark 88.11.2

The completed naive cotangent complex of an adic, topologically finite-type
arrow of `WAdm^{adic*}` is the Jacobian complex of a restricted-power-series
presentation. Morphisms of presentations induce a unique isomorphism in `K(B)`,
and for Noetherian adic `A` the construction reproduces Equation 88.3.0.1 and
is independent of the ideal of definition.
-/

@[expose] public section

open Algebra.NaiveCotangent
open Algebra.NaiveCotangent.Restricted
open CategoryTheory
open HomotopyCategory
open TopologicalRing
open TopologicalRing.Ideal

universe u

namespace Algebra.NaiveCotangent.Restricted

section Definition

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [Algebra A B]
variable {ι : Type u} [Fintype ι]

/-- Remark 88.11.2 (1): Let `A → B` be an arrow of `WAdm^{adic*}` which is adic
and topologically of finite type. Write `B = A{x_ι} / J`. The completed naive
cotangent complex `NL_{B/A}^∧` is the two-term complex
`(J / J² ⟶ ⊕ᵢ B dx_i)` in homological degrees `1` and `0`, with differential
sending the residue of `g ∈ J` to the Jacobian of restricted-power-series
partials `fun i ↦ ∂g / ∂x_i`. -/
@[stacks 0GBX]
noncomputable abbrev naiveCotangent (P : Presentation A B ι) :
    ChainComplex (ModuleCat B) ℕ :=
  complex P

/-- The differential of `NL_{B/A}^∧` in degrees `1 → 0` is the Jacobian of the
restricted presentation. -/
theorem naiveCotangent_d_one_zero (P : Presentation A B ι) :
    (naiveCotangent P).d 1 0 = ModuleCat.ofHom (jacobian P) := sorry

/-- `NL_{B/A}^∧` is the Jacobian complex of the restricted presentation. -/
theorem naiveCotangent_eq (P : Presentation A B ι) :
    naiveCotangent P = complex P := sorry

end Definition

section WellDefined

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A]
variable [CommRing B] [TopologicalSpace B] [Algebra A B]
variable {ι ι' : Type u} [Fintype ι] [Fintype ι']

/-- The morphism in `K(B)` induced by a morphism of restricted presentations,
via the usual formulas on `J / J²` and on `dx_i`. -/
noncomputable def mapNaiveCotangent [IsTopologicalRing A] [IsLinearTopology A A]
    {P : Presentation A B ι} {Q : Presentation A B ι'} (f : Presentation.Hom P Q) :
    (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent P) ⟶
      (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent Q) :=
  (quotient (ModuleCat B) (ComplexShape.down ℕ)).map (chainMap f)

/-- `mapNaiveCotangent` is the image of the induced chain map in `K(B)`. -/
theorem mapNaiveCotangent_def [IsTopologicalRing A] [IsLinearTopology A A]
    {P : Presentation A B ι} {Q : Presentation A B ι'} (f : Presentation.Hom P Q) :
    mapNaiveCotangent f =
      (quotient (ModuleCat B) (ComplexShape.down ℕ)).map (chainMap f) :=
  sorry

/-- Any two morphisms of restricted presentations induce the same morphism in
`K(B)`. -/
theorem mapNaiveCotangent_eq [IsTopologicalRing A] [IsLinearTopology A A]
    {P : Presentation A B ι} {Q : Presentation A B ι'} (f g : Presentation.Hom P Q) :
    mapNaiveCotangent f = mapNaiveCotangent g :=
  sorry

/-- The morphism in `K(B)` induced by a morphism of restricted presentations is
an isomorphism. -/
theorem isIso_mapNaiveCotangent [IsTopologicalRing A] [IsLinearTopology A A]
    {P : Presentation A B ι} {Q : Presentation A B ι'} (f : Presentation.Hom P Q) :
    IsIso (mapNaiveCotangent f) :=
  sorry

/-- Any two restricted presentations of an adic topologically finite-type arrow
of `WAdm^{adic*}` admit a morphism of presentations. -/
theorem hom_nonempty [IsAdicStarRing A] [IsAdicStarRing B]
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (P : Presentation A B ι) (Q : Presentation A B ι') :
    Nonempty (Presentation.Hom P Q) :=
  sorry

/-- Remark 88.11.2 (2): Exactly as in the proof of Lemma 88.3.1, the complex of
`B`-modules `NL_{B/A}^∧` is well defined up to unique isomorphism in the
homotopy category `K(B)`. Morphisms of presentations induce one and the same
isomorphism in `K(B)`. -/
@[stacks 0GBX]
theorem isoUnique [IsAdicStarRing A] [IsAdicStarRing B]
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (P : Presentation A B ι) (Q : Presentation A B ι') :
    Nonempty
      ((quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent P) ≅
        (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent Q)) :=
  sorry

/-- Any two restricted Jacobian complexes of an adic topologically finite-type
arrow of `WAdm^{adic*}` are homotopy equivalent. -/
theorem homotopyEquiv_nonempty [IsAdicStarRing A] [IsAdicStarRing B]
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (P : Presentation A B ι) (Q : Presentation A B ι') :
    Nonempty (HomotopyEquiv (naiveCotangent P) (naiveCotangent Q)) :=
  sorry

/-- Remark 88.11.2 (3): If `A` is Noetherian and `I ⊂ A` is an ideal of
definition, then the restricted construction reproduces the naive cotangent
complex of `B` over `(A, I)` defined by Equation 88.3.0.1, because `A[x_ι]^∧`
agrees with `A{x_ι}` by Formal Spaces, Remark 87.28.2. The identification is
the canonical chain-complex isomorphism induced by `adicEquiv`. -/
@[stacks 0GBX]
noncomputable def reproducesAdic [IsAdicStarRing A] [IsAdicStarRing B]
    [IsNoetherianRing A]
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (I : Ideal A) (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    naiveCotangent P ≅
      Adic.naiveCotangent I (Presentation.toAdic ι I hI P) :=
  complexIso_toAdic ι I hI P

/-- The comparison of Remark 88.11.2 (3) is the chain-complex isomorphism
induced by `adicEquiv`. -/
theorem reproducesAdic_eq [IsAdicStarRing A] [IsAdicStarRing B]
    [IsNoetherianRing A]
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (I : Ideal A) (hI : IsIdealOfDefinition I)
    (P : Presentation A B ι) :
    reproducesAdic hφ h_adic h_tft I hI P = complexIso_toAdic ι I hI P :=
  sorry

end WellDefined

section IndependentOfIdeal

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A]
variable [CommRing B] [TopologicalSpace B] [Algebra A B]
variable {ι ι' : Type u} [Fintype ι] [Fintype ι']

/-- Remark 88.11.2 (4): Still when `A` is an adic Noetherian topological ring,
the object `NL_{B/A}^∧` is independent of the choice of the ideal of
definition `I ⊂ A`. -/
@[stacks 0GBX]
theorem independentOfIdeal [IsAdicStarRing A] [IsAdicStarRing B]
    [IsNoetherianRing A]
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (I I' : Ideal A) (hI : IsIdealOfDefinition I) (hI' : IsIdealOfDefinition I')
    (P_adic : Adic.Presentation A B I ι)
    (Q_adic : Adic.Presentation A B I' ι') :
    Nonempty
      ((quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (Adic.naiveCotangent I P_adic) ≅
        (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (Adic.naiveCotangent I' Q_adic)) :=
  sorry

end IndependentOfIdeal

end Algebra.NaiveCotangent.Restricted
