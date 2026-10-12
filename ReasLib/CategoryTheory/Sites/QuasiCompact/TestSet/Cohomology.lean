/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.QuasiCompact.Sheaf.Representable
public import ReasLib.CategoryTheory.Sites.QuasiCompact.TestSet
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology test sets on a site

This leaf owns the stronger test-set package used for filtered-colimit comparisons of sheaf
cohomology.  The underlying quasi-compact test-set notion and finite representable coproducts
remain in `QuasiCompact.TestSet`; this file only adds the cohomological refinement and its bridge.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet

noncomputable section

universe i vi z v u

namespace CategoryTheory.GrothendieckTopology.Cohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-- A cohomology test set satisfies the local-surjection, product, equalizer, and
quasi-compactness conditions needed for filtered-colimit cohomology. -/
@[mk_iff testSet_iff]
class TestSet (S : Set (Sheaf J (Type (max u v)))) : Prop where
  /-- Some member of the test set covers the terminal sheaf locally. -/
  exists_surjective_to_terminal :
    ∃ K : Sheaf J (Type (max u v)), K ∈ S ∧
      IsLocallySurjective (terminal.from K)
  /-- A locally surjective map into a test object can be refined by another test object. -/
  refine_surjection
      {F K : Sheaf J (Type (max u v))} (π : F ⟶ K)
      (hK : K ∈ S) (hπ : IsLocallySurjective π) :
      ∃ K' : Sheaf J (Type (max u v)), K' ∈ S ∧
        ∃ κ : K' ⟶ F, IsLocallySurjective (κ ≫ π)
  /-- Test objects are closed under products up to a locally surjective cover. -/
  surjective_product
      {K K' : Sheaf J (Type (max u v))} (hK : K ∈ S) (hK' : K' ∈ S) :
      ∃ K'' : Sheaf J (Type (max u v)), K'' ∈ S ∧
        ∃ π : K'' ⟶ K ⨯ K', IsLocallySurjective π
  /-- Equalizers of maps between test objects admit locally surjective test covers. -/
  surjective_equalizer
      {K K' : Sheaf J (Type (max u v))} (a b : K ⟶ K')
      (hK : K ∈ S) (hK' : K' ∈ S) :
      ∃ K'' : Sheaf J (Type (max u v)), K'' ∈ S ∧
        ∃ π : K'' ⟶ equalizer a b, IsLocallySurjective π
  /-- Every member of the test set is quasi-compact. -/
  quasiCompact
      {K : Sheaf J (Type (max u v))} (hK : K ∈ S) :
      K.IsQuasiCompactObject

/-- A cohomology test set is a quasi-compact test set for global sections. -/
@[stacks 0GN3 "cohomology test set implies quasi-compact test set"]
instance TestSet.toQuasiCompactTestSet
    (S : Set (Sheaf J (Type (max u v)))) [TestSet J S] :
    IsQuasiCompactTestSet J S := sorry

section Comparison

variable {I : Type i} [Category.{vi} I] [IsFiltered I]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{z} (Sheaf J AddCommGrpCat.{v})]

/-- Filtered colimits commute with every degree of sheaf cohomology under a cohomology test set. -/
@[stacks 0GN3 "cohomology commutes with filtered colimits from a test set"]
theorem colimitComparison_isIso
    (S : Set (Sheaf J (Type (max u v)))) [TestSet J S]
    (ℱ : I ⥤ Sheaf J AddCommGrpCat.{v}) [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ Sheaf.functorH.{z, v, v, u} J p)] :
    IsIso (colimit.post ℱ (Sheaf.functorH.{z, v, v, u} J p)) := sorry

end Comparison

/-- A basis of site objects satisfying the finite-refinement and equalizer-cover clauses from
the cohomological colimit criterion. -/
@[mk_iff basis_iff]
class Basis (B : Set C) : Prop
    extends QuasiCompact.TestSet.RefiningBasis J B where
  /-- Equalizers of representable maps from `B` admit finite representable coproduct covers. -/
  surjective_equalizer :
    ∀ ⦃U U' : C⦄ (a b : U ⟶ U'), U ∈ B → U' ∈ B →
      ∃ K : Sheaf J (Type (max u v)),
        K ∈ finiteRepresentableCoproducts J B ∧
          ∃ π : K ⟶ equalizer (J.sheafifiedRepresentableMap a)
              (J.sheafifiedRepresentableMap b),
            IsLocallySurjective π

/-- A cohomological basis produces the associated finite representable cohomology test set. -/
@[stacks 0GN4 "finite representable cohomology test set"]
instance Basis.toTestSet (B : Set C) [Basis J B] :
    TestSet J (finiteRepresentableCoproducts J B) := sorry

end CategoryTheory.GrothendieckTopology.Cohomology

end
