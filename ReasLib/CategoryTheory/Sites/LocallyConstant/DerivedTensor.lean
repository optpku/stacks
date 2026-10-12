/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor products with locally constant cohomology

This leaf owns the tensor-closure statement for bounded-above derived sheaves whose cohomology
objects are finite-type locally constant modules.  The cohomology-in predicate is the canonical
derived-category owner; no chapter-specific tensor notation or wrapper property is introduced.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.LocallyConstant.FiniteType.Cohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} Λ))]
variable [MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]

/-- Lemma 21.53.4 (094H), with explicit upper bounds: finite-type locally constant cohomology is
preserved by the derived tensor product of two bounded-above derived sheaves. -/
@[stacks 094H "tensor closure of finite-type locally constant cohomology"]
theorem tensor_of_isLE
    {a b : ℤ}
    {K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    (hK : DerivedCategory.cohomologyIn
      (finiteTypeLocallyConstantModule J Λ) K)
    (hKboundedAbove : K.IsLE a)
    (hL : DerivedCategory.cohomologyIn
      (finiteTypeLocallyConstantModule J Λ) L)
    (hLboundedAbove : L.IsLE b) :
    DerivedCategory.cohomologyIn
      (finiteTypeLocallyConstantModule J Λ) (K ⊗ L) := sorry

/-- The source-facing bounded-above form of Lemma 21.53.4 (094H). -/
@[stacks 094H]
theorem tensor
    {K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    (hK : DerivedCategory.cohomologyIn
      (finiteTypeLocallyConstantModule J Λ) K)
    (hKboundedAbove : (t.minus : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))) K)
    (hL : DerivedCategory.cohomologyIn
      (finiteTypeLocallyConstantModule J Λ) L)
    (hLboundedAbove : (t.minus : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))) L) :
    DerivedCategory.cohomologyIn
      (finiteTypeLocallyConstantModule J Λ) (K ⊗ L) := sorry

end CategoryTheory.Sheaf.LocallyConstant.FiniteType.Cohomology

end
