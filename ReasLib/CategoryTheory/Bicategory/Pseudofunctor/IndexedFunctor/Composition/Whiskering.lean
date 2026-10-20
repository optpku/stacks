/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Composition.Basic

/-!
# Whiskering and horizontal composition of indexed functors
-/

@[expose] public section

universe uC vC uD vD uE vE uI vI uJ vJ uF vF uG vG uH vH uM vM uN vN

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace IndexedFunctor

variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vG, uG}}

/-- Compatibility with reindexing for postcomposition of an indexed-functor modification by a
fixed indexed functor. -/
theorem postcompHom_naturality
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    (T : IndexedFunctor v G L)
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    ((H.comp T).naturality f).hom.app x ≫
        (L.map ((u ⋙ v).map f).op.toLoc).toFunctor.map
          ((Functor.whiskerRight (α.app U) (T.app (u.obj U))).app x) =
      (Functor.whiskerRight (α.app V) (T.app (u.obj V))).app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        ((K.comp T).naturality f).hom.app x := sorry

/-- Postcompose an indexed-functor modification by a fixed indexed functor. -/
noncomputable def postcompHom
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    (T : IndexedFunctor v G L) :
    H.comp T ⟶ K.comp T where
  app U := Functor.whiskerRight (α.app U) (T.app (u.obj U))
  naturality f x := postcompHom_naturality α T f x

/-- Components of postcomposition of an indexed modification are ordinary right-whiskerings. -/
@[simp]
theorem postcompHom_app
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    (T : IndexedFunctor v G L) (U : C) :
    (postcompHom α T).app U =
      Functor.whiskerRight (α.app U) (T.app (u.obj U)) := sorry

/-- Object components of postcomposition of an indexed modification are obtained by mapping the
original component through the fixed indexed functor. -/
@[simp]
theorem postcompHom_app_app
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    (T : IndexedFunctor v G L) (U : C)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    ((postcompHom α T).app U).app x =
      (T.app (u.obj U)).map ((α.app U).app x) := sorry

/-- Postcomposition of the identity indexed modification is the identity. -/
@[simp]
theorem postcompHom_id
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (T : IndexedFunctor v G L) :
    postcompHom (𝟙 H) T = 𝟙 (H.comp T) := sorry

/-- Postcomposition preserves vertical composition of indexed modifications. -/
@[simp]
theorem postcompHom_comp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K M : IndexedFunctor u F G}
    (α : H ⟶ K) (β : K ⟶ M) (T : IndexedFunctor v G L) :
    postcompHom (α ≫ β) T =
      postcompHom α T ≫ postcompHom β T := sorry

/-- Postcomposition by a fixed indexed functor is functorial on indexed functors and their
modifications.

The source reindexing functor `u` and source pseudofunctor `F` are explicit because neither is
determined by the fixed target indexed functor `T`. -/
noncomputable def postcomp
    (u : C ⥤ D) (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF})
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (T : IndexedFunctor v G L) :
    IndexedFunctor u F G ⥤ IndexedFunctor (u ⋙ v) F L where
  obj H := H.comp T
  map α := postcompHom α T
  map_id H := postcompHom_id H T
  map_comp α β := postcompHom_comp α β T

/-- The object action of indexed-functor postcomposition is indexed-functor composition. -/
@[simp]
theorem postcomp_obj
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (T : IndexedFunctor v G L) (H : IndexedFunctor u F G) :
    (postcomp u F T).obj H = H.comp T := sorry

/-- The morphism action of indexed-functor postcomposition is postcomposition of
modifications. -/
@[simp]
theorem postcomp_map
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (T : IndexedFunctor v G L)
    {H K : IndexedFunctor u F G} (α : H ⟶ K) :
    (postcomp u F T).map α = postcompHom α T := sorry

/-- Compatibility with reindexing for precomposition of an indexed-functor modification by a
fixed indexed functor. -/
theorem precompHom_naturality
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G)
    {K T : IndexedFunctor v G L} (α : K ⟶ T)
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    ((H.comp K).naturality f).hom.app x ≫
        (L.map ((u ⋙ v).map f).op.toLoc).toFunctor.map
          ((Functor.whiskerLeft (H.app U) (α.app (u.obj U))).app x) =
      (Functor.whiskerLeft (H.app V) (α.app (u.obj V))).app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        ((H.comp T).naturality f).hom.app x := sorry

/-- Precompose an indexed-functor modification by a fixed indexed functor. -/
noncomputable def precompHom
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G)
    {K T : IndexedFunctor v G L} (α : K ⟶ T) :
    H.comp K ⟶ H.comp T where
  app U := Functor.whiskerLeft (H.app U) (α.app (u.obj U))
  naturality f x := precompHom_naturality H α f x

/-- Components of precomposition of an indexed modification are ordinary left-whiskerings. -/
@[simp]
theorem precompHom_app
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G)
    {K T : IndexedFunctor v G L} (α : K ⟶ T) (U : C) :
    (precompHom H α).app U =
      Functor.whiskerLeft (H.app U) (α.app (u.obj U)) := sorry

/-- Object components of precomposition of an indexed modification evaluate the original
component after the fixed indexed functor. -/
@[simp]
theorem precompHom_app_app
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G)
    {K T : IndexedFunctor v G L} (α : K ⟶ T) (U : C)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    ((precompHom H α).app U).app x =
      (α.app (u.obj U)).app ((H.app U).obj x) := sorry

/-- Precomposition of the identity indexed modification is the identity. -/
@[simp]
theorem precompHom_id
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L) :
    precompHom H (𝟙 K) = 𝟙 (H.comp K) := sorry

/-- Precomposition preserves vertical composition of indexed modifications. -/
@[simp]
theorem precompHom_comp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G)
    {K T M : IndexedFunctor v G L} (α : K ⟶ T) (β : T ⟶ M) :
    precompHom H (α ≫ β) =
      precompHom H α ≫ precompHom H β := sorry

/-- Precomposition by a fixed indexed functor is functorial on indexed functors and their
modifications.

The target reindexing functor `v` and target pseudofunctor `L` are explicit because neither is
determined by the fixed source indexed functor `H`. -/
noncomputable def precomp
    {E : Type uE} [Category.{vE} E] (v : D ⥤ E)
    (L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH})
    (H : IndexedFunctor u F G) :
    IndexedFunctor v G L ⥤ IndexedFunctor (u ⋙ v) F L where
  obj K := H.comp K
  map α := precompHom H α
  map_id K := precompHom_id H K
  map_comp α β := precompHom_comp H α β

/-- The object action of indexed-functor precomposition is indexed-functor composition. -/
@[simp]
theorem precomp_obj
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L) :
    (precomp v L H).obj K = H.comp K := sorry

/-- The morphism action of indexed-functor precomposition is precomposition of
modifications. -/
@[simp]
theorem precomp_map
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G)
    {K T : IndexedFunctor v G L} (α : K ⟶ T) :
    (precomp v L H).map α = precompHom H α := sorry

/-- Horizontal composition of indexed-functor modifications. -/
noncomputable def compHom
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    {T M : IndexedFunctor v G L} (β : T ⟶ M) :
    H.comp T ⟶ K.comp M :=
  postcompHom α T ≫ precompHom K β

/-- Horizontal composition can equivalently be formed by first whiskering on the left and then
on the right. This is the interchange law for indexed-functor modifications. -/
theorem compHom_eq_precomp_postcomp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    {T M : IndexedFunctor v G L} (β : T ⟶ M) :
    compHom α β = precompHom H β ≫ postcompHom α M := sorry

/-- Components of horizontal composition are the ordinary horizontal composites of the
component natural transformations. -/
@[simp]
theorem compHom_app
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    {T M : IndexedFunctor v G L} (β : T ⟶ M) (U : C) :
    (compHom α β).app U =
      Functor.whiskerRight (α.app U) (T.app (u.obj U)) ≫
        Functor.whiskerLeft (K.app U) (β.app (u.obj U)) := sorry

/-- Object components of horizontal composition first apply the fixed target functor to the
left component and then the right component. -/
@[simp]
theorem compHom_app_app
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    {T M : IndexedFunctor v G L} (β : T ⟶ M) (U : C)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    ((compHom α β).app U).app x =
      (T.app (u.obj U)).map ((α.app U).app x) ≫
        (β.app (u.obj U)).app ((K.app U).obj x) := sorry

/-- Horizontal composition with an identity on the left is left whiskering. -/
@[simp]
theorem compHom_id_left
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G)
    {T M : IndexedFunctor v G L} (β : T ⟶ M) :
    compHom (𝟙 H) β = precompHom H β := sorry

/-- Horizontal composition with an identity on the right is right whiskering. -/
@[simp]
theorem compHom_id_right
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    (T : IndexedFunctor v G L) :
    compHom α (𝟙 T) = postcompHom α T := sorry

/-- Horizontal composition of two identity modifications is the identity. -/
@[simp]
theorem compHom_id_id
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (T : IndexedFunctor v G L) :
    compHom (𝟙 H) (𝟙 T) = 𝟙 (H.comp T) := sorry

/-- Horizontal composition respects simultaneous vertical composition. -/
@[simp]
theorem compHom_comp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K N : IndexedFunctor u F G} (α : H ⟶ K) (α' : K ⟶ N)
    {T M P : IndexedFunctor v G L} (β : T ⟶ M) (β' : M ⟶ P) :
    compHom (α ≫ α') (β ≫ β') =
      compHom α β ≫ compHom α' β' := sorry

/-- Composition of indexed functors is functorial simultaneously in both indexed-functor
variables.

All five base data are explicit because this owner has no active indexed-functor input from
which Lean could recover them. -/
noncomputable def compFunctor
    (u : C ⥤ D) (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF})
    (G : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vG, uG})
    {E : Type uE} [Category.{vE} E] (v : D ⥤ E)
    (L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}) :
    IndexedFunctor u F G × IndexedFunctor v G L ⥤
      IndexedFunctor (u ⋙ v) F L where
  obj P := P.1.comp P.2
  map f := compHom f.1 f.2
  map_id P := compHom_id_id P.1 P.2
  map_comp f g := compHom_comp f.1 g.1 f.2 g.2

/-- The object action of the indexed-functor composition functor is composition. -/
@[simp]
theorem compFunctor_obj
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (T : IndexedFunctor v G L) :
    (compFunctor u F G v L).obj (H, T) = H.comp T := sorry

/-- The morphism action of the indexed-functor composition functor is horizontal composition. -/
@[simp]
theorem compFunctor_map
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {H K : IndexedFunctor u F G} (α : H ⟶ K)
    {T M : IndexedFunctor v G L} (β : T ⟶ M) :
    (compFunctor u F G v L).map ((α, β) : (H, T) ⟶ (K, M)) = compHom α β := sorry


end IndexedFunctor

end Pseudofunctor.LocallyDiscreteOpToCat

end CategoryTheory
