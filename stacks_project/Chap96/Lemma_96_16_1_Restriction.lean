module

public import Mathlib.Algebra.Category.Grp.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import stacks_project.Chap96.Lemma_96_16_1_Pullback

/-!
# Small-étale restriction of an inverse-image sheaf

The restriction `F|_{U_étale}` of an étale sheaf on a groupoid fibration is
the small-to-big inverse image of `x⁻¹ F` along the identity of `U = p(x)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {𝒳 : GroupoidsOver S}

/-- Restriction of an étale sheaf `F` on `𝒳` to the small étale site of
`U = p(x)`, as the small-to-big inverse image of `pullbackSheaf .etale x F`. -/
def restrictEtaleSheaf (x : 𝒳.total)
    (F : Sheaf 𝒳.etaleTopology AddCommGrpCat.{u}) :
    Sheaf ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u} :=
  ((Scheme.Etale.SmallToBig.relocalizationFunctor (𝟙 (𝒳.p.obj x).left)).sheafPushforwardContinuous
      AddCommGrpCat.{u} ((𝒳.p.obj x).left.smallEtaleTopology)
      (StandardTopology.etale.overTopology (𝒳.p.obj x).left)).obj
    (pullbackSheaf .etale x F)

/-- The underlying presheaf of `restrictEtaleSheaf x F` is
`restrictEtalePresheaf x F.obj`. -/
theorem restrictEtaleSheaf_obj (x : 𝒳.total)
    (F : Sheaf 𝒳.etaleTopology AddCommGrpCat.{u}) :
    (restrictEtaleSheaf x F).obj = restrictEtalePresheaf x F.obj :=
  sorry

/-- `restrictEtaleSheaf x F` is the small-to-big inverse image of
`pullbackSheaf .etale x F`. -/
theorem restrictEtaleSheaf_eq (x : 𝒳.total)
    (F : Sheaf 𝒳.etaleTopology AddCommGrpCat.{u}) :
    restrictEtaleSheaf x F =
      ((Scheme.Etale.SmallToBig.relocalizationFunctor
          (𝟙 (𝒳.p.obj x).left)).sheafPushforwardContinuous
          AddCommGrpCat.{u} ((𝒳.p.obj x).left.smallEtaleTopology)
          (StandardTopology.etale.overTopology (𝒳.p.obj x).left)).obj
        (pullbackSheaf .etale x F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
