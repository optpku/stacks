/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Index
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Simplicial copower bifunctors

Copower is jointly functorial after restricting the indexing simplicial sets along any functor
whose values admit the required copowers. The identity indexing functor gives the global
simplicial-set/simplicial-object bifunctor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u e d

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- `HasCopowers.OfIndex K C` records copowers by every simplicial set in the image of `K`,
uniformly in the simplicial object. It is the simplicial specialization of the generic
indexed-coproduct owner used by `copower.ofIndex`. -/
@[stacks 017E "copowers along an indexing functor"]
abbrev HasCopowers.OfIndex {D : Type d} [Category.{e} D]
    (K : D ⥤ SSet.{w}) (C : Type u) [Category.{v} C] : Prop :=
  Functor.HasIndexedCoprods.OfIndex K C

namespace HasCopowers.OfIndex

/-- Categories with all `w`-small coproducts admit copowers along every simplicial
indexing functor. -/
@[stacks 017E "indexed simplicial copowers from coproducts"]
instance ofCoproducts {D : Type d} [Category.{e} D] [HasCoproducts.{w} C]
    (K : D ⥤ SSet.{w}) : HasCopowers.OfIndex K C := sorry

end HasCopowers.OfIndex

section Bifunctor

variable {D : Type d} [Category.{e} D]
variable (K : D ⥤ SSet.{w})
variable [HasCopowers.OfIndex K C]

/-- Identity law for the index-variable natural transformations along an indexing functor. -/
@[stacks 017E "indexed copower functor identity"]
theorem copower.ofIndex.map.id (d : D) :
    copower.indexHom.natTrans (C := C) (K.map (𝟙 d)) =
      𝟙 (copower.functor (C := C) (K.obj d)) := sorry

/-- Composition law for the index-variable natural transformations along an indexing functor. -/
@[stacks 017E "indexed copower functor composition"]
theorem copower.ofIndex.map.comp {d₁ d₂ d₃ : D} (f : d₁ ⟶ d₂) (g : d₂ ⟶ d₃) :
    copower.indexHom.natTrans (C := C) (K.map (f ≫ g)) =
      copower.indexHom.natTrans (C := C) (K.map f) ≫
        copower.indexHom.natTrans (C := C) (K.map g) := sorry

/-- Copower is a curried bifunctor after restricting the indexing simplicial sets along a
functor `K` for which the required coproducts exist. -/
@[stacks 017E "curried simplicial copower bifunctor"]
abbrev copower.ofIndex : D ⥤ SimplicialObject C ⥤ SimplicialObject C :=
  Functor.indexedCoprod.bifunctor (C := C) K

/-- Evaluating `copower.ofIndex K` on both variables gives the corresponding copower. -/
@[simp, stacks 017E "indexed copower object formula"]
theorem copower.ofIndex.obj (d : D) (X : SimplicialObject C) :
    ((copower.ofIndex K).obj d).obj X = copower (K.obj d) X := sorry

/-- The action of `copower.ofIndex K` on a morphism in the simplicial-object variable. -/
@[simp, stacks 017E "indexed copower object-variable map formula"]
theorem copower.ofIndex.obj.map (d : D) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    ((copower.ofIndex K).obj d).map f = copower.hom (K.obj d) f := sorry

/-- The component of `copower.ofIndex K` on a morphism in its indexing variable. -/
@[simp, stacks 017E "indexed copower map formula"]
theorem copower.ofIndex.map.app {d d' : D} (f : d ⟶ d')
    (X : SimplicialObject C) :
    ((copower.ofIndex K).map f).app X = copower.indexHom X (K.map f) := sorry

end Bifunctor

section GlobalBifunctor

variable [HasCopowers.OfIndex (𝟭 SSet.{w}) C]

/-- Copower as a bifunctor, covariant in arbitrary simplicial sets and simplicial objects. -/
@[stacks 017E "simplicial copower bifunctor"]
abbrev copower.bifunctor :
    SSet.{w} ⥤ SimplicialObject C ⥤ SimplicialObject C :=
  copower.ofIndex (C := C) (𝟭 SSet.{w})

/-- Evaluating the copower bifunctor on both variables gives the corresponding copower. -/
@[simp, stacks 017E "copower bifunctor object formula"]
theorem copower.bifunctor.obj (U : SSet.{w}) (X : SimplicialObject C) :
    ((copower.bifunctor (C := C)).obj U).obj X = copower U X := sorry

/-- The action of the copower bifunctor on a morphism in the simplicial-object variable. -/
@[simp, stacks 017E "copower bifunctor object-variable map formula"]
theorem copower.bifunctor.obj.map (U : SSet.{w})
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    ((copower.bifunctor (C := C)).obj U).map f = copower.hom U f := sorry

/-- The component of the copower bifunctor on a morphism in its simplicial-set variable. -/
@[simp, stacks 017E "copower bifunctor index-map formula"]
theorem copower.bifunctor.map.app {U V : SSet.{w}} (a : U ⟶ V)
    (X : SimplicialObject C) :
    ((copower.bifunctor (C := C)).map a).app X = copower.indexHom X a := sorry

end GlobalBifunctor

end CategoryTheory.SimplicialObject
