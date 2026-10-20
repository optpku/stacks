module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite
public import Mathlib.CategoryTheory.Sites.Continuous

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

variable {S : Scheme.{u}} {W X : AlgebraicSpace S}

/-- Composing an étale chart with a representably étale morphism gives an étale chart. -/
theorem postcompose_obj_isEtale (ι : W ⟶ X) (h_etale : Representable.Etale ι)
    (U : site W) : Representable.Etale (U.hom ≫ ι) := sorry

/-- A commuting chart morphism still commutes after postcomposition. -/
theorem postcompose_map_w (ι : W ⟶ X)
    {U V : site W} (map : U ⟶ V) :
    yoneda.map map.left ≫ (V.hom ≫ ι) = U.hom ≫ ι := sorry

/-- Postcomposition on chart morphisms preserves identities. -/
theorem postcompose_map_id (ι : W ⟶ X) (h_etale : Representable.Etale ι)
    (U : site W) :
    let chart : site X := MorphismProperty.CostructuredArrow.mk ⊤ (U.hom ≫ ι)
      (postcompose_obj_isEtale ι h_etale U)
    (MorphismProperty.CostructuredArrow.homMk (𝟙 U.left) trivial
      (postcompose_map_w ι (𝟙 U)) : chart ⟶ chart) = 𝟙 chart := sorry

/-- Postcomposition on chart morphisms preserves composition. -/
theorem postcompose_map_comp (ι : W ⟶ X) (h_etale : Representable.Etale ι)
    {U V T : site W} (map : U ⟶ V) (next : V ⟶ T) :
    let source : site X := MorphismProperty.CostructuredArrow.mk ⊤ (U.hom ≫ ι)
      (postcompose_obj_isEtale ι h_etale U)
    let middle : site X := MorphismProperty.CostructuredArrow.mk ⊤ (V.hom ≫ ι)
      (postcompose_obj_isEtale ι h_etale V)
    let target : site X := MorphismProperty.CostructuredArrow.mk ⊤ (T.hom ≫ ι)
      (postcompose_obj_isEtale ι h_etale T)
    (MorphismProperty.CostructuredArrow.homMk (map ≫ next).left trivial
      (postcompose_map_w ι (map ≫ next)) : source ⟶ target) =
      (MorphismProperty.CostructuredArrow.homMk map.left trivial
        (postcompose_map_w ι map) : source ⟶ middle) ≫
      (MorphismProperty.CostructuredArrow.homMk next.left trivial
        (postcompose_map_w ι next) : middle ⟶ target) := sorry

/-- A representably étale morphism induces a postcomposition functor between small étale
chart categories. -/
def postcompose (ι : W ⟶ X) (h_etale : Representable.Etale ι) : site W ⥤ site X where
  obj U := MorphismProperty.CostructuredArrow.mk ⊤ (U.hom ≫ ι)
    (postcompose_obj_isEtale ι h_etale U)
  map map := MorphismProperty.CostructuredArrow.homMk map.left trivial
    (postcompose_map_w ι map)
  map_id := postcompose_map_id ι h_etale
  map_comp := postcompose_map_comp ι h_etale

/-- Postcomposition by a representably étale morphism is continuous for small étale
topologies. -/
instance postcompose_isContinuous (ι : W ⟶ X) (h_etale : Representable.Etale ι) :
    Functor.IsContinuous (postcompose ι h_etale) (topology W) (topology X) := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
