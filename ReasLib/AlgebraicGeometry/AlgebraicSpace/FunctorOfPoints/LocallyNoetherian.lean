/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.Objects

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.StandardTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The functor of points of an algebraic space `X` over `S`, restricted to
locally Noetherian schemes over `S`. On objects it sends `V` to
`Mor_S(V, X) = ofOver V ⟶ X`. -/
def homOnLocallyNoetherian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1) where
  obj V := ofOver V.unop.obj ⟶ X
  map φ := ofHom fun f ↦ ofOverMap φ.unop.hom ≫ f
  map_id := by
    intro V
    apply ConcreteCategory.hom_ext
    intro f
    change yoneda.map (𝟙 V.unop.obj) ≫ f = f
    rw [yoneda.map_id, Category.id_comp]
  map_comp := by
    intro V1 V2 V3 φ ψ
    apply ConcreteCategory.hom_ext
    intro f
    change yoneda.map (ψ.unop.hom ≫ φ.unop.hom) ≫ f =
      yoneda.map ψ.unop.hom ≫ (yoneda.map φ.unop.hom ≫ f)
    rw [yoneda.map_comp, Category.assoc]

/-- The object map of `homOnLocallyNoetherian X` is `Mor_S(V, X)`. -/
theorem homOnLocallyNoetherian_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (V : (locallyNoetherian S).FullSubcategory) :
    (homOnLocallyNoetherian X).obj (op V) = (ofOver V.obj ⟶ X) :=
  rfl

/-- The morphism map of `homOnLocallyNoetherian X` is precomposition with
`ofOverMap`. -/
theorem homOnLocallyNoetherian_map {S : Scheme.{u}} (X : AlgebraicSpace S)
    {V1 V2 : (locallyNoetherian S).FullSubcategory} (φ : V2 ⟶ V1)
    (f : ofOver V1.obj ⟶ X) :
    (homOnLocallyNoetherian X).map φ.op f = ofOverMap φ.hom ≫ f :=
  rfl

/-- `homOnLocallyNoetherian X` is the restriction of the universe-raised functor
of points of `X` to locally Noetherian schemes over `S`. -/
def homOnLocallyNoetherian_isoUlift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    homOnLocallyNoetherian X ≅
      (restrictPresheaf S).obj
        (X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  NatIso.ofComponents
    (fun V ↦
      { hom := ofHom fun f ↦ ULift.up (yonedaEquiv f)
        inv := ofHom fun x ↦ yonedaEquiv.symm x.down
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro f
          exact yonedaEquiv.symm_apply_apply f
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro x
          exact congrArg ULift.up (yonedaEquiv.apply_symm_apply x.down) })
    (by
      intro V1 V2 φ
      apply ConcreteCategory.hom_ext
      intro f
      apply ULift.ext
      exact (yonedaEquiv_naturality f φ.unop.hom).symm)

/-- Components of `homOnLocallyNoetherian_isoUlift` are Yoneda evaluation into
`ULift`. -/
theorem homOnLocallyNoetherian_isoUlift_hom_app {S : Scheme.{u}}
    (X : AlgebraicSpace S) (V : (locallyNoetherian S).FullSubcategory)
    (f : ofOver V.obj ⟶ X) :
    ((homOnLocallyNoetherian_isoUlift X).hom.app (op V) f).down =
      yonedaEquiv f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
