/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Lemma_93_10_3_Deformation
public import stacks_project.Chap93.Lemma_93_10_3_Sequence

/-!
# Canonical exact sequence of Inf and T for morphisms of schemes

In Example 93.9.1, a morphism `f : X ⟶ Y` of schemes over `k` determines a
canonical exact sequence of `k`-vector spaces relating `Inf` and `T` of
`Def_{X ⟶ Y}` from Example 93.10.1 with `Inf`/`T` of `Def_X × Def_Y`,
`Der_k(O_Y, f_* O_X)`, and `Ext¹_{O_X}(Lf^* NL_{Y/k}, O_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FlatSchemeMorphismCat

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
variable (hf : f ≫ hY = hX)
variable [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]

/-- Lemma 93.10.3 (1)
In Example 93.9.1 let `f : X ⟶ Y` be a morphism of schemes over `k`. The forgetful
map `Inf(Def_{X ⟶ Y}) ⟶ Inf(Def_X) × Inf(Def_Y)` is injective. -/
@[stacks 0E3V]
theorem infToProdInf_injective :
    Function.Injective (infToProdInf Λ k f hX hY hf) := sorry

/-- Lemma 93.10.3 (2)
The sequence `Inf(Def_{X ⟶ Y}) ⟶ Inf(Def_X) × Inf(Def_Y) ⟶ Der_k(O_Y, f_* O_X)`
is exact. -/
@[stacks 0E3V]
theorem exact_inf_prodInf_der :
    Function.Exact (infToProdInf Λ k f hX hY hf)
      (prodInfToDer Λ k f hX hY hf) := sorry

/-- Lemma 93.10.3 (3)
The sequence `Inf(Def_X) × Inf(Def_Y) ⟶ Der_k(O_Y, f_* O_X) ⟶ T Def_{X ⟶ Y}`
is exact. -/
@[stacks 0E3V]
theorem exact_prodInf_der_tangent :
    Function.Exact (prodInfToDer Λ k f hX hY hf)
      (derToTangent Λ k f hX hY hf) := sorry

/-- Lemma 93.10.3 (4)
The sequence `Der_k(O_Y, f_* O_X) ⟶ T Def_{X ⟶ Y} ⟶ T Def_X × T Def_Y` is exact. -/
@[stacks 0E3V]
theorem exact_der_tangent_prodTangent :
    Function.Exact (derToTangent Λ k f hX hY hf)
      (tangentToProdTangent Λ k f hX hY hf) := sorry

/-- Lemma 93.10.3 (5)
The sequence `T Def_{X ⟶ Y} ⟶ T Def_X × T Def_Y ⟶ Ext¹_{O_X}(Lf^* NL_{Y/k}, O_X)`
is exact. The last arrow need not be surjective. -/
@[stacks 0E3V]
theorem exact_prodTangent_ext :
    Function.Exact (tangentToProdTangent Λ k f hX hY hf)
      (prodTangentToExt Λ k f hX hY hf) := sorry
