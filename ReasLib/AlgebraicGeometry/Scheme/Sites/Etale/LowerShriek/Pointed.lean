/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Pointed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Pointed

/-!
# Compactly supported direct image of pointed étale sheaves

The pointed compact-support direct image is obtained by sheafifying the colimit of its supported-section diagram.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}}

/-- The presheaf of compactly supported pointed sections over admissible supports. -/
def pointedLowerShriekPresheaf (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}] :
    Sheaf X.smallEtaleTopology Pointed.{u} ⥤ Y.Etaleᵒᵖ ⥤ Pointed.{u} where
  obj G :=
    { obj := fun V ↦ colimit (pointedAdmissibleDiagram f G V.unop)
      map := fun {V W} g ↦
        colimMap (pointedAdmissibleRestriction f G g.unop) ≫
          colimit.pre (pointedAdmissibleDiagram f G W.unop)
            (FiniteSupport.Admissible.pullbackFunctor f g.unop)
      map_id := sorry
      map_comp := sorry }
  map {G H} φ :=
    { app := fun V ↦
        colimMap
          { app := fun A ↦
              { toFun := fun s ↦
                  ⟨(φ.hom.app (op (mk (A.ambient.ι ≫
                      baseChangeToSource f V.unop)))).toFun s.1, sorry⟩
                map_point := sorry }
            naturality := sorry }
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- The value of the compact-support presheaf is the colimit of supported sections. -/
theorem pointedLowerShriekPresheaf_obj (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    (G : Sheaf X.smallEtaleTopology Pointed.{u}) (V : Y.Etale) :
    ((pointedLowerShriekPresheaf f).obj G).obj (op V) =
      colimit (pointedAdmissibleDiagram f G V) := rfl

/-- The compact-support direct image on pointed sheaves. -/
def pointedLowerShriek (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}] :
    Sheaf X.smallEtaleTopology Pointed.{u} ⥤ Sheaf Y.smallEtaleTopology Pointed.{u} :=
  pointedLowerShriekPresheaf f ⋙ presheafToSheaf Y.smallEtaleTopology Pointed.{u}

/-- The value of pointed lower shriek is the sheafification of its presheaf. -/
theorem pointedLowerShriek_obj (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    (G : Sheaf X.smallEtaleTopology Pointed.{u}) :
    (pointedLowerShriek f).obj G =
      (presheafToSheaf Y.smallEtaleTopology Pointed.{u}).obj
        ((pointedLowerShriekPresheaf f).obj G) := rfl

/-- The compact-support direct image on pointed sheaves has a right adjoint. -/
instance pointedLowerShriek_isLeftAdjoint (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}] :
    (pointedLowerShriek f).IsLeftAdjoint := sorry

/-- The stalk of pointed lower shriek is the coproduct of the fibre stalks. -/
theorem pointedLowerShriekStalkIso_nonempty (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}] (ybar : GeometricPoint Y) :
    Nonempty (pointedLowerShriek f ⋙ (GeometricPoint.toSmallEtalePoint ybar).sheafFiber ≅
      pointedStalkCoproduct f ybar) := sorry

end AlgebraicGeometry.Scheme.Etale

end
