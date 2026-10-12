/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cones Into Pointwise Categorical Pullbacks

This leaf sends an indexed functor into a pointwise categorical pullback to its
compatible projected cone.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe uC vC uD vD uE vE uF vF uG vG uH vH uK vK

namespace CategoryTheory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]
variable {u : C ⥤ D} {v : E ⥤ C}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable {H : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vH, uH}}

/-- The component compatibility isomorphism obtained from an indexed functor into a pointwise
categorical pullback. -/
@[stacks 0040 "fiberwise compatibility of a cone into a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.Cone.isoApp
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R))
    (U : E) :
    (((T.comp (Pullback.Fst.indexedFunctor L R)).comp L).app U) ≅
      (((T.comp (Pullback.Snd.indexedFunctor L R)).comp R).app U) :=
  ((CategoricalPullback.toCatCommSqOver (L.app (v.obj U)) (R.app (v.obj U))
    (K.obj (LocallyDiscrete.mk (op U)))).obj (T.app U)).iso

/-- The component compatibility isomorphisms of an indexed functor into a pointwise pullback
commute with base reindexing. -/
theorem Pullback.Cone.isoApp.naturality
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R))
    {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (((T.comp (Pullback.Fst.indexedFunctor L R)).comp L).naturality f).hom.app x ≫
        (H.map ((v ⋙ u).map f).op.toLoc).toFunctor.map
          ((Pullback.Cone.isoApp L R T U).hom.app x) =
      (Pullback.Cone.isoApp L R T V).hom.app
          ((K.map f.op.toLoc).toFunctor.obj x) ≫
        (((T.comp (Pullback.Snd.indexedFunctor L R)).comp R).naturality f).hom.app x := sorry

/-- An indexed functor into a pointwise categorical pullback determines an indexed compatibility
isomorphism between its two projections. -/
@[stacks 0040 "indexed compatibility of a cone into a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.Cone.iso
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    (T.comp (Pullback.Fst.indexedFunctor L R)).comp L ≅
      (T.comp (Pullback.Snd.indexedFunctor L R)).comp R :=
  IndexedFunctor.mkIso
    (Pullback.Cone.isoApp L R T)
    (fun f x ↦ Pullback.Cone.isoApp.naturality L R T f x)

/-- The component of the indexed compatibility isomorphism induced by a functor into a
pointwise pullback is the canonical categorical-pullback square. -/
@[simp]
theorem Pullback.Cone.iso.app
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R))
    (U : E) :
    IndexedFunctor.isoApp (Pullback.Cone.iso L R T) U =
      Pullback.Cone.isoApp L R T U := sorry

/-- The categorical-pullback cone encoded by an indexed functor into the pointwise pullback. -/
@[stacks 0040 "cone object induced by a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.Cone.obj
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    (postcomp v K L) ⊡ (postcomp v K R) where
  fst := T.comp (Pullback.Fst.indexedFunctor L R)
  snd := T.comp (Pullback.Snd.indexedFunctor L R)
  iso := Pullback.Cone.iso L R T

/-- The first indexed functor in the cone encoded by a functor into the pointwise pullback is
postcomposition with the first projection. -/
@[simp]
theorem Pullback.Cone.obj.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    (Pullback.Cone.obj L R T).fst =
      T.comp (Pullback.Fst.indexedFunctor L R) := sorry

/-- The second indexed functor in the cone encoded by a functor into the pointwise pullback is
postcomposition with the second projection. -/
@[simp]
theorem Pullback.Cone.obj.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    (Pullback.Cone.obj L R T).snd =
      T.comp (Pullback.Snd.indexedFunctor L R) := sorry

/-- The structural isomorphism in the cone encoded by a functor into the pointwise pullback is
the canonical indexed compatibility isomorphism. -/
@[simp]
theorem Pullback.Cone.obj.iso
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    (Pullback.Cone.obj L R T).iso = Pullback.Cone.iso L R T := sorry

/-- Compatibility of the two projected modifications induced by a modification between indexed
functors into a pointwise pullback. -/
theorem Pullback.Cone.map.w
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {T S : IndexedFunctor v K (Pullback.pseudofunctor L R)}
    (α : T ⟶ S) :
    (postcomp v K L).map
          (postcompHom α (Pullback.Fst.indexedFunctor L R)) ≫
        (Pullback.Cone.iso L R S).hom =
      (Pullback.Cone.iso L R T).hom ≫
        (postcomp v K R).map
          (postcompHom α (Pullback.Snd.indexedFunctor L R)) := sorry

/-- A modification into the pointwise pullback induces a morphism of its two projected
categorical-pullback cones. -/
@[stacks 0040 "cone morphism induced by a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.Cone.map
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {T S : IndexedFunctor v K (Pullback.pseudofunctor L R)}
    (α : T ⟶ S) :
    Pullback.Cone.obj L R T ⟶ Pullback.Cone.obj L R S where
  fst := postcompHom α (Pullback.Fst.indexedFunctor L R)
  snd := postcompHom α (Pullback.Snd.indexedFunctor L R)
  w := Pullback.Cone.map.w L R α

/-- The first component of the cone morphism induced by an indexed modification is its
postcomposition with the first projection. -/
@[simp]
theorem Pullback.Cone.map.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {T S : IndexedFunctor v K (Pullback.pseudofunctor L R)}
    (α : T ⟶ S) :
    (Pullback.Cone.map L R α).fst =
      postcompHom α (Pullback.Fst.indexedFunctor L R) := sorry

/-- The second component of the cone morphism induced by an indexed modification is its
postcomposition with the second projection. -/
@[simp]
theorem Pullback.Cone.map.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {T S : IndexedFunctor v K (Pullback.pseudofunctor L R)}
    (α : T ⟶ S) :
    (Pullback.Cone.map L R α).snd =
      postcompHom α (Pullback.Snd.indexedFunctor L R) := sorry

/-- The projected-cone construction preserves identity modifications. -/
theorem Pullback.Cone.map.id
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    Pullback.Cone.map L R (𝟙 T) = 𝟙 (Pullback.Cone.obj L R T) := sorry

/-- The projected-cone construction preserves composition of modifications. -/
theorem Pullback.Cone.map.comp
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {T S Q : IndexedFunctor v K (Pullback.pseudofunctor L R)}
    (α : T ⟶ S) (β : S ⟶ Q) :
    Pullback.Cone.map L R (α ≫ β) =
      Pullback.Cone.map L R α ≫ Pullback.Cone.map L R β := sorry

variable (K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}) in
/-- Indexed functors into a pointwise categorical pullback map functorially to compatible pairs
of indexed functors into its two legs. -/
@[stacks 0040 "cone functor for a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.Cone.functor
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H) :
    IndexedFunctor v K (Pullback.pseudofunctor L R) ⥤
      (postcomp v K L) ⊡ (postcomp v K R) where
  obj T := Pullback.Cone.obj L R T
  map α := Pullback.Cone.map L R α
  map_id T := Pullback.Cone.map.id L R T
  map_comp α β := Pullback.Cone.map.comp L R α β

/-- The object action of the pointwise-pullback cone functor is the pair of projected indexed
functors with their canonical compatibility isomorphism. -/
@[simp]
theorem Pullback.Cone.functor.obj
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    (Pullback.Cone.functor K L R).obj T = Pullback.Cone.obj L R T := sorry

/-- The first leg of the cone functor's object action is postcomposition with the first indexed
projection. -/
@[simp]
theorem Pullback.Cone.functor.obj.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    ((Pullback.Cone.functor K L R).obj T).fst =
      T.comp (Pullback.Fst.indexedFunctor L R) := sorry

/-- The second leg of the cone functor's object action is postcomposition with the second
indexed projection. -/
@[simp]
theorem Pullback.Cone.functor.obj.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    ((Pullback.Cone.functor K L R).obj T).snd =
      T.comp (Pullback.Snd.indexedFunctor L R) := sorry

/-- The structural isomorphism of the cone functor's object action is the canonical indexed
compatibility isomorphism. -/
@[simp]
theorem Pullback.Cone.functor.obj.iso
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (T : IndexedFunctor v K (Pullback.pseudofunctor L R)) :
    ((Pullback.Cone.functor K L R).obj T).iso =
      Pullback.Cone.iso L R T := sorry

/-- The morphism action of the pointwise-pullback cone functor is projection of indexed
modifications. -/
@[simp]
theorem Pullback.Cone.functor.map
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {T S : IndexedFunctor v K (Pullback.pseudofunctor L R)}
    (α : T ⟶ S) :
    (Pullback.Cone.functor K L R).map α = Pullback.Cone.map L R α := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
