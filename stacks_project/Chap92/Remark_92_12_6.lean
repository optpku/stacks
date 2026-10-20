/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
public import stacks_project.Chap92.Lemma_92_4_1_Evaluation
public import stacks_project.Chap92.Remark_92_5_5_Resolutions_Resolution
public import stacks_project.Chap92.Remark_92_11_5_Tor
public import stacks_project.Chap92.Remark_92_12_6_LengthTwo
public import stacks_project.Chap92.Remark_92_12_6_MulKer
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-two identifications of the cotangent complex

Remark 92.12.6 records that `Tor_2^{P_n}(B, B) = Tor_1^{P_n}(J_n, B) = Ker(J_n ⊗ J_n → J_n²)`,
that `H^{-2}(L_{B/A})` is the cokernel of `d0 - d1` on a resolution, the length-two `B`-linear
splitting of `Tor_2^{P_1}(B, B)` with middle summand `⊕_t (J_0/J_0²)`, and the exact sequence
`∧²_B(J_0/J_0²) → Tor_2^{P_0}(B, B) → H^{-2}(L_{B/A}) → 0`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Algebra
open Algebra.CotangentComplex
open Algebra.PolynomialSite
open Algebra.Presentation.LengthTwo
open CommAlgCat.Over.Polynomial.Site
open scoped Simplicial TensorProduct

noncomputable section

universe u

namespace Algebra.CotangentComplex

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Tor_2^P(B, B) as left-derived extension of scalars of `B` along `P ⟶ B`. -/
noncomputable def torTwoObjWith (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    ModuleCat.{u} B :=
  ((ModuleCat.extendScalars (algebraMap X.obj.left B)).leftDerived 2).obj
    (ModuleCat.of X.obj.left B)

/-- Tor_2^P(B, B) of a polynomial arrow `P ⟶ B`. -/
noncomputable def torTwoObj (X : Algebra.PolynomialOver A B) : ModuleCat.{u} B :=
  @torTwoObjWith A B _ _ _ X (algebraToBase X)

/-- Unfolding `torTwoObj` recovers the unbundled left-derived extension of scalars. -/
theorem torTwoObj_eq (X : Algebra.PolynomialOver A B) :
    torTwoObj X = @torTwoObjWith A B _ _ _ X (algebraToBase X) :=
  sorry

/-- Remark 92.12.6 (1). For a surjective polynomial arrow `P ⟶ B` one has
`Tor_2^P(B, B) = Tor_1^P(Ker(P ⟶ B), B)`. -/
@[stacks 09D6]
theorem torTwo_isIsomorphic_kernelTor (X : Algebra.PolynomialOver A B)
    (h : Function.Surjective X.obj.hom.hom.toRingHom) :
    IsIsomorphic (torTwoObj X) (kernelTorObj 1 X) :=
  sorry

/-- Remark 92.12.6 (2). For a surjective polynomial arrow `P ⟶ B` one has
`Tor_1^P(Ker(P ⟶ B), B) = Ker(J ⊗_P J → J²)` with `J = Ker(P ⟶ B)`. -/
@[stacks 09D6]
theorem kernelTor_isIsomorphic_mulKer (X : Algebra.PolynomialOver A B)
    (h : Function.Surjective X.obj.hom.hom.toRingHom) :
    IsIsomorphic (kernelTorObj 1 X) (mulKerModuleCat X.obj.hom.hom.toRingHom h) :=
  sorry

/-- Degreewise polynomiality of a resolution of `B` over `A`. -/
theorem resolution_isPolynomial
    {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
    [IsResolution ε] (n : SimplexCategoryᵒᵖ) :
    IsPolynomial A (P.obj n) :=
  sorry

/-- The polynomial simplicial object of a resolution of `B` over `A`. -/
noncomputable def resolutionPolynomialSimplicial
    {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
    [IsResolution ε] :
    SimplicialObject (PolynomialOver A B) :=
  asPolynomialSimplicial ε (resolution_isPolynomial ε)

/-- The map `d0 - d1` on objectwise `Tor_1^P(J, B)` of a resolution. -/
noncomputable def kernelTorFaceSub
    {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
    [IsResolution ε] :
    kernelTorObj 1 ((resolutionPolynomialSimplicial ε) _⦋1⦌) ⟶
      kernelTorObj 1 ((resolutionPolynomialSimplicial ε) _⦋0⦌) :=
  kernelTorMap 1 ((resolutionPolynomialSimplicial ε).δ (0 : Fin 2)) -
    kernelTorMap 1 ((resolutionPolynomialSimplicial ε).δ (1 : Fin 2))

/-- Remark 92.12.6 (3). For a resolution `P_•` of `B` over `A`, `H^{-2}(L_{B/A})` is
canonically the cokernel of `Tor_2^{P_1}(B, B) → Tor_2^{P_0}(B, B)` induced by `d0 - d1`. -/
@[stacks 09D6]
theorem cotangentHomology_negTwo_isIsomorphic_coker_faceSub
    {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
    [IsResolution ε] :
    IsIsomorphic ((Algebra.cotangentComplex A B).homology (-2))
      (cokernel (kernelTorFaceSub ε)) :=
  sorry

end Algebra.CotangentComplex

namespace Algebra.Presentation.LengthTwo

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Remark 92.12.6 (4). For the length-two presentation of Example 92.5.9,
`Tor_2^{P_1}(B, B)` splits as the `B`-module coproduct of `∧²(⊕_t B)`,
`⊕_t (J_0/J_0²)`, and `Tor_2^{P_0}(B, B)`. -/
@[stacks 09D6]
noncomputable def torTwoTerm1Coprod_linearEquiv (P : Presentation A B ι σ) :
    ((⋀[B]^2 (σ →₀ B)) × (σ →₀ P.ker.Cotangent) × mulKer P.ker) ≃ₗ[B]
      mulKer (term1Ker P) :=
  torTwoTerm1LinearEquiv P

/-- The `B`-linear equivalence of Remark 92.12.6 (4) has forward map `torTwoTerm1CoprodLM`. -/
theorem torTwoTerm1Coprod_linearEquiv_toLinearMap (P : Presentation A B ι σ) :
    (torTwoTerm1Coprod_linearEquiv P).toLinearMap = torTwoTerm1CoprodLM P :=
  sorry

/-- Remark 92.12.6 (5). There is an exact sequence
`∧²_{P_0/J_0}(J_0/J_0²) → Tor_2^{P_0}(B, B) → Coker(d0 - d1) → 0`. -/
@[stacks 09D6]
theorem exact_conormalExteriorSquare_cokerFaceSub (P : Presentation A B ι σ) :
    Function.Exact (conormalExteriorSquareToMulKer P.ker) (cokerFaceSubMkQ P) :=
  sorry

/-- Remark 92.12.6 (6). The cokernel of `d0 - d1` on `Tor_2^{P_0}(B, B)` identifies with
`H^{-2}(L_{B/A})`. -/
@[stacks 09D6]
theorem cokerFaceSub_isIsomorphic_cotangentHomology_negTwo (P : Presentation A B ι σ) :
    IsIsomorphic (cokerFaceSubModuleCat P) ((Algebra.cotangentComplex A B).homology (-2)) :=
  sorry

end Algebra.Presentation.LengthTwo
