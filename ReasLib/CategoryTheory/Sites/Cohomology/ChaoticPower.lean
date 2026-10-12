/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.Sites.Chaotic
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Zero

/-!
# Positive-power complexes on chaotic sites

The canonical self-product simplicial object gives the cochain complex used to compute
cohomology on a chaotic site from an object receiving a morphism from every object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject.ZeroCoskeleton

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf.ChaoticPower

variable {C : Type u} [Category.{v} C]

/-- Evaluate the canonical positive-power simplicial object in an abelian sheaf and form its
alternating coface cochain complex. -/
noncomputable abbrev positivePowerComplex
    (X : C) [HasBinaryProducts C]
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}) :
    CochainComplex AddCommGrpCat.{w} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w}).obj
    ((selfProduct X).rightOp ⋙
      (sheafToPresheaf (⊥ : GrothendieckTopology C)
      AddCommGrpCat.{w}).obj F)

/-- For the chaotic topology, the total cohomology of an abelian sheaf is computed by the
positive-power complex associated to an object receiving a morphism from every object. -/
theorem totalCohomology_isomorphic_positivePowerComplex
    (X : C) (hX : ∀ Y : C, Nonempty (Y ⟶ X)) [HasBinaryProducts C]
    (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w})
    [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}]
    [HasInjectiveResolutions (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w})] :
    IsIsomorphic
      (((Sheaf.Γ (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}).rightDerivedToHomotopyCategory ⋙
        ComplexShape.embeddingUpNat.extendHomotopyFunctor AddCommGrpCat.{w} ⋙
        DerivedCategory.Qh).obj F)
      (DerivedCategory.Q.obj ((positivePowerComplex X F).extend ComplexShape.embeddingUpNat)) := sorry

end CategoryTheory.Sheaf.ChaoticPower

end
