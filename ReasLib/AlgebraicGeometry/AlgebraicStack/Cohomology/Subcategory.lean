module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Subcategory
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology on atlas-containing full subcategories

Restriction to a full subcategory containing a smooth surjective atlas and
stable under the relevant scheme morphisms preserves abelian sheaf cohomology
for the étale and fppf topologies.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe z w u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- If `X` is an algebraic stack over `S` and `Q` is a full
subcategory of `X` stable under morphisms lying over smooth morphisms of
schemes and containing a smooth surjective atlas object, then for every
abelian sheaf `F` on `X_étale` and every `p ≥ 0` the cohomology of `F` agrees
with the cohomology of its restriction `g⁻¹ F` on the induced étale site of
`Q`. Here `g⁻¹` is restriction along the inclusion, i.e.
`sheafPushforwardContinuous`. -/
@[stacks 07AK]
theorem cohomologySubcategoryEtale {X : GroupoidsOver S} [AlgebraicStack X]
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))]
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

/-- If `X` is an algebraic stack over `S` and `Q` is a full
subcategory of `X` stable under morphisms lying over flat and locally finitely
presented morphisms of schemes and containing a smooth surjective atlas
object, then for every abelian sheaf `F` on `X_fppf` and every `p ≥ 0` the
cohomology of `F` agrees with the cohomology of its restriction `g⁻¹ F` on
the induced fppf site of `Q`. Here `g⁻¹` is restriction along the inclusion,
i.e. `sheafPushforwardContinuous`. -/
@[stacks 07AK]
theorem cohomologySubcategoryFppf {X : GroupoidsOver S} [AlgebraicStack X]
    (Q : ObjectProperty X.total)
    [Q.InheritedFromTarget
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
        (X.p ⋙ Over.forget S))]
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
