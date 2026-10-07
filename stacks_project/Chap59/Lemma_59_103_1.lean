module

public import stacks_project.Chap59.Lemma_59_39_2
public import stacks_project.Chap59.Lemma_59_103_2_Big
public import stacks_project.Chap59.Lemma_59_103_2_Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme

/-- Lemma 59.103.1 (1): for a sheaf `F` on `S_étale` and `f : X ⟶ S`, the
inverse image `π_S⁻¹ F` on `(Sch/S)_étale` evaluates at `Over.mk f` as the
global sections `Γ(X, f_small⁻¹ F)` on `X_étale`. -/
@[stacks 0EW8]
theorem siteMorphismInverseImage_obj_etale_h {S X : Scheme.{u}} (f : X ⟶ S)
    [HasSheafify X.smallEtaleTopology (Type (u + 1))]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1.obj (op (Over.mk f)) =
      (((Etale.SmallToBig.smallMorphism f)⁻¹).obj F).1.obj (op (globalEtale X)) :=
  sorry

/-- Lemma 59.103.1 (2): for a sheaf `F` on `S_étale`, the inverse image
`π_S⁻¹ F` is a sheaf for the h topology on schemes over `S`. -/
@[stacks 0EW8]
theorem siteMorphismInverseImage_isSheaf_h (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Presheaf.IsSheaf (H.Big.site S)
      (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1 := sorry

/-- Lemma 59.103.1 (3): for a sheaf `F` on `S_étale`, the inverse image
`π_S⁻¹ F` is a fortiori a sheaf for the étale topology on schemes over `S`. -/
@[stacks 0EW8]
theorem siteMorphismInverseImage_isSheaf_etale_of_h (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Presheaf.IsSheaf (S.overGrothendieckTopology @Etale)
      (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1 := sorry

/-- Lemma 59.103.1 (4): on `(Sch/S)_h`, the sheaf given by the Γ-rule is
`ε_S⁻¹ π_S⁻¹ F`, where `ε_S` is the morphism of topoi from the big h site
to the big étale site. -/
@[stacks 0EW8]
theorem toHInverseImage_etalePiInverseImage (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    ((HComparison.epsilon S)⁻¹).obj
        (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F) =
      ⟨(((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1,
        siteMorphismInverseImage_isSheaf_h S F⟩ := sorry

end AlgebraicGeometry.Scheme
