module

public import stacks_project.Chap59.Lemma_59_39_2
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Comparison
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme

/-- Lemma 59.102.1 (1): for a sheaf `F` on `S_étale` and `f : X ⟶ S`, the
inverse image `π_S⁻¹ F` on `(Sch/S)_étale` evaluates at `Over.mk f` as the
global sections `Γ(X, f_small⁻¹ F)` on `X_étale`. -/
@[stacks 0DDW]
theorem siteMorphismInverseImage_obj_etale_ph {S X : Scheme.{u}} (f : X ⟶ S)
    [HasSheafify X.smallEtaleTopology (Type (u + 1))]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1.obj (op (Over.mk f)) =
      (((Etale.SmallToBig.smallMorphism f)⁻¹).obj F).1.obj (op (globalEtale X)) :=
  sorry

/-- Lemma 59.102.1 (2): for a sheaf `F` on `S_étale`, the inverse image
`π_S⁻¹ F` is a sheaf for the ph topology on schemes over `S`. -/
@[stacks 0DDW]
theorem siteMorphismInverseImage_isSheaf_ph (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Presheaf.IsSheaf (Scheme.bigPhSite S)
      (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1 := sorry

/-- Lemma 59.102.1 (3): for a sheaf `F` on `S_étale`, the inverse image
`π_S⁻¹ F` is a fortiori a sheaf for the étale topology on schemes over `S`. -/
@[stacks 0DDW]
theorem siteMorphismInverseImage_isSheaf_etale_of_ph (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Presheaf.IsSheaf (S.overGrothendieckTopology @Etale)
      (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1 := sorry

/-- Lemma 59.102.1 (4): on `(Sch/S)_ph`, the sheaf given by the Γ-rule is
`ε_S⁻¹ π_S⁻¹ F`, where `ε_S` is the morphism of topoi from the big ph site
to the big étale site. -/
@[stacks 0DDW]
theorem toPhInverseImage_etalePiInverseImage (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    ((PhComparison.standardComparison .etale S)⁻¹).obj
        (((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F) =
      ⟨(((Etale.SmallToBig.siteMorphismOfTopoi S)⁻¹).obj F).1,
        siteMorphismInverseImage_isSheaf_ph S F⟩ := sorry

end AlgebraicGeometry.Scheme
