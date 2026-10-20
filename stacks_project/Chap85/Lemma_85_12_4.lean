module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_12_4_Descent
public import stacks_project.Chap85.Lemma_85_12_4_Equivalence

/-!
# Lemma 85.12.4

In Situation 85.3.3, cartesian sheaves of sets (resp. abelian groups) on `C_total`
are equivalent to pairs `(F, α)` consisting of a sheaf on `C_0` and an isomorphism
`α : (f_{δ 1})⁻¹ F ≅ (f_{δ 0})⁻¹ F` on `C_1` satisfying the `C_2` cocycle.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial
open CategoryTheory.SimplicialSites
open CategoryTheory.SimplicialSites.Sheaf

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Lemma 85.12.4 (1)
In Situation 85.3.3, the category of cartesian sheaves of sets on `C_total` is
equivalent to the category of pairs `(F, α)` where `F` is a sheaf of sets on
`C_0` and `α : (f_{δ 1})⁻¹ F ≅ (f_{δ 0})⁻¹ F` is an isomorphism of sheaves of
sets on `C_1` such that `(f_{δ 1})⁻¹ α = (f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` as maps
of sheaves on `C_2`. -/
@[stacks 0D7I]
def sheafCartesianEquivalence :
    Cartesian C J (Type w) ≌ FaceDescent C J (Type w) :=
  cartesianEquivalence C J (Type w)

/-- The forward functor of `sheafCartesianEquivalence` extracts the pair `(F_0, α)`. -/
theorem sheafCartesianEquivalence_functor :
    (sheafCartesianEquivalence C J).functor = toDescentFunctor C J (Type w) :=
  sorry

/-- The inverse functor of `sheafCartesianEquivalence` assembles a cartesian sheaf of sets
from a pair `(F, α)`. -/
theorem sheafCartesianEquivalence_inverse :
    (sheafCartesianEquivalence C J).inverse = ofDescentFunctor C J (Type w) :=
  sorry

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Lemma 85.12.4 (2)
In Situation 85.3.3, the category of cartesian sheaves of abelian groups on `C_total`
is equivalent to the category of pairs `(F, α)` where `F` is a sheaf of abelian
groups on `C_0` and `α : (f_{δ 1})⁻¹ F ≅ (f_{δ 0})⁻¹ F` is an isomorphism of
sheaves of abelian groups on `C_1` such that
`(f_{δ 1})⁻¹ α = (f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` as maps of sheaves on `C_2`. -/
@[stacks 0D7I]
def abelianCartesianEquivalence :
    Cartesian C J AddCommGrpCat.{w} ≌ FaceDescent C J AddCommGrpCat.{w} :=
  cartesianEquivalence C J AddCommGrpCat.{w}

/-- The forward functor of `abelianCartesianEquivalence` extracts the pair `(F_0, α)`. -/
theorem abelianCartesianEquivalence_functor :
    (abelianCartesianEquivalence C J).functor =
      toDescentFunctor C J AddCommGrpCat.{w} :=
  sorry

/-- The inverse functor of `abelianCartesianEquivalence` assembles a cartesian sheaf of
abelian groups from a pair `(F, α)`. -/
theorem abelianCartesianEquivalence_inverse :
    (abelianCartesianEquivalence C J).inverse =
      ofDescentFunctor C J AddCommGrpCat.{w} :=
  sorry

end Abelian

end CategoryTheory.SimplicialSites
