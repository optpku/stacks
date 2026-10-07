module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local bounded models for derived sheaves

This leaf owns the reusable predicate saying that the restriction of a derived sheaf object has a
bounded model by finite-type locally constant sheaves, and the cover-wise existence theorem.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.DerivedRestriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]

/-- The exact derived restriction of a sheaf object to the slice site over `U`. -/
noncomputable abbrev obj
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (U : C)
    [Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ))]
    [(J.overPullback (ModuleCat.{w} Λ) U).Additive]
    [PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)]
    [PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)] :
    DerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory.obj K

/-- Stacks 094G: on `U`, the derived restriction of `K` has a bounded complex model whose terms
are finite-type locally constant sheaves. -/
@[stacks 094G "local bounded finite-type locally constant model"]
def HasBoundedFiniteTypeLocallyConstantModelOn
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (U : C)
    [∀ V : Over U, HasWeakSheafify ((J.over U).over V) (ModuleCat.{w} Λ)]
    [Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ))]
    [(J.overPullback (ModuleCat.{w} Λ) U).Additive]
    [PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)]
    [PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)] : Prop :=
  ∃ P : CochainComplex.Bounded (Sheaf (J.over U) (ModuleCat.{w} Λ)),
    ∃ _ : DerivedCategory.Q.obj P.obj ≅ obj K U,
      ∀ n : ℤ, IsFiniteTypeLocallyConstantModule (P.obj.X n)

/-- Witness form of `HasBoundedFiniteTypeLocallyConstantModelOn`. -/
theorem hasBoundedFiniteTypeLocallyConstantModelOn_iff
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (U : C)
    [∀ V : Over U, HasWeakSheafify ((J.over U).over V) (ModuleCat.{w} Λ)]
    [Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ))]
    [(J.overPullback (ModuleCat.{w} Λ) U).Additive]
    [PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)]
    [PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)] :
    HasBoundedFiniteTypeLocallyConstantModelOn K U ↔
      ∃ P : CochainComplex.Bounded (Sheaf (J.over U) (ModuleCat.{w} Λ)),
        ∃ _ : DerivedCategory.Q.obj P.obj ≅ obj K U,
          ∀ n : ℤ, IsFiniteTypeLocallyConstantModule (P.obj.X n) := sorry

variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [∀ U : C, HasDerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) (ModuleCat.{w} Λ)]
variable [∀ U : C, (J.overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)]
variable [∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)]
variable [IsNoetherianRing Λ]

/-- A bounded derived object with finite-type locally constant cohomology acquires a bounded
finite-type locally constant model after passing to a cover of any object. -/
@[stacks 094G "over an arbitrary object"]
theorem exists_cover_model
    (X : C) (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (hKbounded : (t.bounded : ObjectProperty
      (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))) K)
    (hK : DerivedCategory.cohomologyIn (finiteTypeLocallyConstantModule J Λ) K) :
    ∃ T : J.Cover X, ∀ I : T.Arrow,
      HasBoundedFiniteTypeLocallyConstantModelOn K I.Y := sorry

/-- Lemma 21.53.1 (094G): a bounded derived object with finite-type locally constant cohomology
has bounded finite-type locally constant models over a cover of the terminal object. -/
@[stacks 094G]
theorem exists_cover_model_terminal
    [HasTerminal C] (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (hKbounded : (t.bounded : ObjectProperty
      (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))) K)
    (hK : DerivedCategory.cohomologyIn (finiteTypeLocallyConstantModule J Λ) K) :
    ∃ T : J.Cover (⊤_ C), ∀ I : T.Arrow,
      HasBoundedFiniteTypeLocallyConstantModelOn K I.Y := sorry

end CategoryTheory.Sheaf.DerivedRestriction
