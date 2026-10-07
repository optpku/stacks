module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}} {G H H' : ModuleValuedFunctor.{u, v} A}

/-- The module of pairs whose images under two morphisms of module-valued functors agree. -/
def pullbackObj (g : Hom G H) (α : Hom H' H) (B : Under A) :
    ModuleCat.{v} B.right :=
  ModuleCat.of B.right <| LinearMap.eqLocus
    ((g.app B).hom.comp (LinearMap.fst B.right (G.obj B) (H'.obj B)))
    ((α.app B).hom.comp (LinearMap.snd B.right (G.obj B) (H'.obj B)))

/-- Transition maps preserve the defining equality of the pointwise pullback. -/
theorem pullbackMap_mem (g : Hom G H) (α : Hom H' H) {B B' : Under A}
    (f : B ⟶ B') (x : pullbackObj g α B) :
    (G.map f x.1.1, H'.map f x.1.2) ∈
      LinearMap.eqLocus
        ((g.app B').hom.comp (LinearMap.fst B'.right (G.obj B') (H'.obj B')))
        ((α.app B').hom.comp (LinearMap.snd B'.right (G.obj B') (H'.obj B'))) := sorry

/-- The underlying transition function on a pointwise pullback. -/
noncomputable def pullbackMapFun (g : Hom G H) (α : Hom H' H) {B B' : Under A}
    (f : B ⟶ B') (x : pullbackObj g α B) : pullbackObj g α B' :=
  ⟨(G.map f x.1.1, H'.map f x.1.2), pullbackMap_mem g α f x⟩

/-- Pointwise pullback transition functions preserve addition. -/
theorem pullbackMap_add (g : Hom G H) (α : Hom H' H) {B B' : Under A}
    (f : B ⟶ B') (x y : pullbackObj g α B) :
    pullbackMapFun g α f (x + y) =
      pullbackMapFun g α f x + pullbackMapFun g α f y := sorry

/-- Pointwise pullback transition functions are semilinear over the base map. -/
theorem pullbackMap_smul (g : Hom G H) (α : Hom H' H) {B B' : Under A}
    (f : B ⟶ B') (b : B.right) (x : pullbackObj g α B) :
    pullbackMapFun g α f (b • x) =
      f.right.hom b • pullbackMapFun g α f x := sorry

/-- The semilinear transition map on a pointwise pullback. -/
noncomputable def pullbackMap (g : Hom G H) (α : Hom H' H) {B B' : Under A}
    (f : B ⟶ B') : pullbackObj g α B →ₛₗ[f.right.hom] pullbackObj g α B' where
  toFun := pullbackMapFun g α f
  map_add' := pullbackMap_add g α f
  map_smul' := pullbackMap_smul g α f

/-- Pointwise pullback transition along an identity is the identity. -/
theorem pullback_map_id (g : Hom G H) (α : Hom H' H) (B : Under A)
    (x : pullbackObj g α B) :
    pullbackMap g α (𝟙 B) x = x := sorry

/-- Pointwise pullback transition respects composition. -/
theorem pullback_map_comp (g : Hom G H) (α : Hom H' H) {B B' B'' : Under A}
    (f : B ⟶ B') (f' : B' ⟶ B'') (x : pullbackObj g α B) :
    pullbackMap g α (f ≫ f') x =
      pullbackMap g α f' (pullbackMap g α f x) := sorry

/-- The pointwise pullback of two morphisms of module-valued functors with common codomain. -/
noncomputable def pullback (g : Hom G H) (α : Hom H' H) : ModuleValuedFunctor.{u, v} A where
  obj := pullbackObj g α
  map f := ModuleCat.semilinearMapAddEquiv f.right.hom _ _ (pullbackMap g α f)
  map_id B x := pullback_map_id g α B x
  map_comp f f' x := pullback_map_comp g α f f' x

/-- The first pointwise projection commutes with transition maps. -/
theorem pullbackFst_naturality (g : Hom G H) (α : Hom H' H) {B B' : Under A}
    (f : B ⟶ B') (x : pullbackObj g α B) :
    G.map f
        (ModuleCat.ofHom
          ((LinearMap.fst B.right (G.obj B) (H'.obj B)).comp
            (LinearMap.eqLocus
              ((g.app B).hom.comp (LinearMap.fst B.right (G.obj B) (H'.obj B)))
              ((α.app B).hom.comp
                (LinearMap.snd B.right (G.obj B) (H'.obj B)))).subtype) x) =
      ModuleCat.ofHom
        ((LinearMap.fst B'.right (G.obj B') (H'.obj B')).comp
          (LinearMap.eqLocus
            ((g.app B').hom.comp (LinearMap.fst B'.right (G.obj B') (H'.obj B')))
            ((α.app B').hom.comp
              (LinearMap.snd B'.right (G.obj B') (H'.obj B')))).subtype)
        (ModuleCat.semilinearMapAddEquiv f.right.hom _ _ (pullbackMap g α f) x) := sorry

/-- The first projection from a pointwise pullback. -/
noncomputable def pullbackFst (g : Hom G H) (α : Hom H' H) : Hom (pullback g α) G where
  app B := ModuleCat.ofHom <|
    (LinearMap.fst B.right (G.obj B) (H'.obj B)).comp
      (LinearMap.eqLocus
        ((g.app B).hom.comp (LinearMap.fst B.right (G.obj B) (H'.obj B)))
        ((α.app B).hom.comp (LinearMap.snd B.right (G.obj B) (H'.obj B)))).subtype
  naturality f x := pullbackFst_naturality g α f x

/-- The second pointwise projection commutes with transition maps. -/
theorem pullbackSnd_naturality (g : Hom G H) (α : Hom H' H) {B B' : Under A}
    (f : B ⟶ B') (x : pullbackObj g α B) :
    H'.map f
        (ModuleCat.ofHom
          ((LinearMap.snd B.right (G.obj B) (H'.obj B)).comp
            (LinearMap.eqLocus
              ((g.app B).hom.comp (LinearMap.fst B.right (G.obj B) (H'.obj B)))
              ((α.app B).hom.comp
                (LinearMap.snd B.right (G.obj B) (H'.obj B)))).subtype) x) =
      ModuleCat.ofHom
        ((LinearMap.snd B'.right (G.obj B') (H'.obj B')).comp
          (LinearMap.eqLocus
            ((g.app B').hom.comp (LinearMap.fst B'.right (G.obj B') (H'.obj B')))
            ((α.app B').hom.comp
              (LinearMap.snd B'.right (G.obj B') (H'.obj B')))).subtype)
        (ModuleCat.semilinearMapAddEquiv f.right.hom _ _ (pullbackMap g α f) x) := sorry

/-- The second projection from a pointwise pullback. -/
noncomputable def pullbackSnd (g : Hom G H) (α : Hom H' H) : Hom (pullback g α) H' where
  app B := ModuleCat.ofHom <|
    (LinearMap.snd B.right (G.obj B) (H'.obj B)).comp
      (LinearMap.eqLocus
        ((g.app B).hom.comp (LinearMap.fst B.right (G.obj B) (H'.obj B)))
        ((α.app B).hom.comp (LinearMap.snd B.right (G.obj B) (H'.obj B)))).subtype
  naturality f x := pullbackSnd_naturality g α f x

/-- The value of the pointwise pullback is the submodule of pairs with equal images. -/
theorem pullback_obj (g : Hom G H) (α : Hom H' H) (B : Under A) :
    (pullback g α).obj B = pullbackObj g α B := sorry

/-- The first pullback projection sends a compatible pair to its first component. -/
theorem pullback_fst_app (g : Hom G H) (α : Hom H' H) (B : Under A)
    (x : pullbackObj g α B) :
    (pullbackFst g α).app B x = x.1.1 := sorry

/-- The second pullback projection sends a compatible pair to its second component. -/
theorem pullback_snd_app (g : Hom G H) (α : Hom H' H) (B : Under A)
    (x : pullbackObj g α B) :
    (pullbackSnd g α).app B x = x.1.2 := sorry

/-- The two projections from the pointwise pullback have equal composites to the codomain. -/
theorem pullback_condition (g : Hom G H) (α : Hom H' H) (B : Under A)
    (x : pullbackObj g α B) :
    g.app B ((pullbackFst g α).app B x) =
      α.app B ((pullbackSnd g α).app B x) := sorry

end ModuleValuedFunctor
