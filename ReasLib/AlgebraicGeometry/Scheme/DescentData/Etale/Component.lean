/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Etale

variable {S' S : Scheme.{u}}

/-- The component morphism associated to an identity morphism is the identity
  morphism of the corresponding étale scheme. -/
theorem componentFunctorMap_id (f : S' ⟶ S) (D : Etale f) :
    (MorphismProperty.Over.homMk
        ((𝟙 D : D ⟶ D).hom.hom PUnit.unit).left
        (Over.w ((𝟙 D : D ⟶ D).hom.hom PUnit.unit)) :
      Scheme.Etale.mk (D.obj.obj PUnit.unit).hom ⟶
        Scheme.Etale.mk (D.obj.obj PUnit.unit).hom) =
      𝟙 (Scheme.Etale.mk (D.obj.obj PUnit.unit).hom) := sorry

/-- The component morphism associated to a composite is the composite of the
  corresponding component morphisms. -/
theorem componentFunctorMap_comp (f : S' ⟶ S) {D E F : Etale f}
    (g : D ⟶ E) (h : E ⟶ F) :
    (MorphismProperty.Over.homMk
        ((g ≫ h).hom.hom PUnit.unit).left
        (Over.w ((g ≫ h).hom.hom PUnit.unit)) :
      Scheme.Etale.mk (D.obj.obj PUnit.unit).hom ⟶
        Scheme.Etale.mk (F.obj.obj PUnit.unit).hom) =
      (MorphismProperty.Over.homMk
          (g.hom.hom PUnit.unit).left
          (Over.w (g.hom.hom PUnit.unit)) :
        Scheme.Etale.mk (D.obj.obj PUnit.unit).hom ⟶
          Scheme.Etale.mk (E.obj.obj PUnit.unit).hom) ≫
        (MorphismProperty.Over.homMk
          (h.hom.hom PUnit.unit).left
          (Over.w (h.hom.hom PUnit.unit)) :
          Scheme.Etale.mk (E.obj.obj PUnit.unit).hom ⟶
            Scheme.Etale.mk (F.obj.obj PUnit.unit).hom) := sorry

/-- The étale component functor extracts the unique component scheme. -/
noncomputable def componentFunctor (f : S' ⟶ S) : Etale f ⥤ S'.Etale where
  obj D := Scheme.Etale.mk (D.obj.obj PUnit.unit).hom
  map g := MorphismProperty.Over.homMk
    (g.hom.hom PUnit.unit).left (Over.w (g.hom.hom PUnit.unit))
  map_id := componentFunctorMap_id f
  map_comp := componentFunctorMap_comp f

/-- The component functor sends a descent datum to its unique étale scheme over
  the covering scheme. -/
theorem componentFunctor_obj (f : S' ⟶ S) (D : Etale f) :
    (componentFunctor f).obj D = Scheme.Etale.mk (D.obj.obj PUnit.unit).hom := sorry

end Etale
end DescentData
end Scheme
end AlgebraicGeometry

end
