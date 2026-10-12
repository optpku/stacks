/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_23_3_Subcategory

/-!
# Lemma 96.23.3

Cohomology of an algebraic stack is unchanged after restriction to a full
subcategory that is stable under morphisms lying over smooth (resp. flat and
locally finitely presented) scheme maps and that contains a smooth surjective
atlas object. The inclusion is continuous and cocontinuous, and `g⁻¹` on
abelian sheaves is restriction along the inclusion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe z w u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The inclusion of a full subcategory stable under morphisms lying over
smooth scheme maps is continuous for the induced étale topologies. -/
instance inclusion_isContinuous_etale {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [IsStableUnderOver X (@Smooth : MorphismProperty Scheme.{u}) Q] :
    Q.ι.IsContinuous (subcategoryTopology X StandardTopology.etale Q)
      X.etaleTopology :=
  sorry

/-- The inclusion of a full subcategory stable under morphisms lying over
smooth scheme maps is cocontinuous for the induced étale topologies. -/
instance inclusion_isCocontinuous_etale {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [IsStableUnderOver X (@Smooth : MorphismProperty Scheme.{u}) Q] :
    Q.ι.IsCocontinuous (subcategoryTopology X StandardTopology.etale Q)
      X.etaleTopology :=
  sorry

/-- The inclusion of a full subcategory stable under morphisms lying over
flat and locally finitely presented scheme maps is continuous for the induced
fppf topologies. -/
instance inclusion_isContinuous_fppf {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [IsStableUnderOver X
      ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u}) Q] :
    Q.ι.IsContinuous (subcategoryTopology X StandardTopology.fppf Q)
      X.fppfTopology :=
  sorry

/-- The inclusion of a full subcategory stable under morphisms lying over
flat and locally finitely presented scheme maps is cocontinuous for the induced
fppf topologies. -/
instance inclusion_isCocontinuous_fppf {X : GroupoidsOver S}
    (Q : ObjectProperty X.total)
    [IsStableUnderOver X
      ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u}) Q] :
    Q.ι.IsCocontinuous (subcategoryTopology X StandardTopology.fppf Q)
      X.fppfTopology :=
  sorry

/-- Lemma 96.23.3 (1): if `X` is an algebraic stack over `S` and `Q` is a full
subcategory of `X` stable under morphisms lying over smooth morphisms of
schemes and containing a smooth surjective atlas object, then for every
abelian sheaf `F` on `X_étale` and every `p ≥ 0` the cohomology of `F` agrees
with the cohomology of its restriction `g⁻¹ F` on the induced étale site of
`Q`. Here `g⁻¹` is restriction along the inclusion, i.e.
`sheafPushforwardContinuous`. -/
@[stacks 07AK]
theorem cohomologySubcategoryEtale {X : GroupoidsOver S} [AlgebraicStack X]
    (Q : ObjectProperty X.total)
    [IsStableUnderOver X (@Smooth : MorphismProperty Scheme.{u}) Q]
    (h_atlas : ExistsSmoothSurjectiveObject Q)
    [HasSheafify X.etaleTopology AddCommGrpCat.{max w u}]
    [HasSheafify (subcategoryTopology X StandardTopology.etale Q)
      AddCommGrpCat.{max w u}]
    [HasExt.{z} (Sheaf X.etaleTopology AddCommGrpCat.{max w u})]
    [HasExt.{z}
      (Sheaf (subcategoryTopology X StandardTopology.etale Q)
        AddCommGrpCat.{max w u})]
    (F : Sheaf X.etaleTopology AddCommGrpCat.{max w u}) (p : ℕ) :
    IsIsomorphic
      ((Sheaf.functorH (subcategoryTopology X StandardTopology.etale Q) p).obj
        ((Q.ι.sheafPushforwardContinuous AddCommGrpCat.{max w u}
            (subcategoryTopology X StandardTopology.etale Q)
            X.etaleTopology).obj F))
      ((Sheaf.functorH X.etaleTopology p).obj F) :=
  sorry

/-- Lemma 96.23.3 (2): if `X` is an algebraic stack over `S` and `Q` is a full
subcategory of `X` stable under morphisms lying over flat and locally finitely
presented morphisms of schemes and containing a smooth surjective atlas
object, then for every abelian sheaf `F` on `X_fppf` and every `p ≥ 0` the
cohomology of `F` agrees with the cohomology of its restriction `g⁻¹ F` on
the induced fppf site of `Q`. Here `g⁻¹` is restriction along the inclusion,
i.e. `sheafPushforwardContinuous`. -/
@[stacks 07AK]
theorem cohomologySubcategoryFppf {X : GroupoidsOver S} [AlgebraicStack X]
    (Q : ObjectProperty X.total)
    [IsStableUnderOver X
      ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u}) Q]
    (h_atlas : ExistsSmoothSurjectiveObject Q)
    [HasSheafify X.fppfTopology AddCommGrpCat.{max w u}]
    [HasSheafify (subcategoryTopology X StandardTopology.fppf Q)
      AddCommGrpCat.{max w u}]
    [HasExt.{z} (Sheaf X.fppfTopology AddCommGrpCat.{max w u})]
    [HasExt.{z}
      (Sheaf (subcategoryTopology X StandardTopology.fppf Q)
        AddCommGrpCat.{max w u})]
    (F : Sheaf X.fppfTopology AddCommGrpCat.{max w u}) (p : ℕ) :
    IsIsomorphic
      ((Sheaf.functorH (subcategoryTopology X StandardTopology.fppf Q) p).obj
        ((Q.ι.sheafPushforwardContinuous AddCommGrpCat.{max w u}
            (subcategoryTopology X StandardTopology.fppf Q)
            X.fppfTopology).obj F))
      ((Sheaf.functorH X.fppfTopology p).obj F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
