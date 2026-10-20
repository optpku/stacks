module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of truncated simplicial copowers

Truncated simplicial copowers inherit the full object-variable, index-variable, natural
transformation, and bifunctorial API directly from generic indexed coproducts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u e d

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]
variable {n : ℕ}

section ObjectVariable

variable (U : SSet.Truncated.{w} n)
variable {W W' : SimplicialObject.Truncated C n}

/-- The raw component of the truncated copower morphism induced by a morphism in the
truncated simplicial-object variable. -/
@[stacks 017E "truncated copower induced component"]
abbrev copower.homApp
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (copower U W).obj Δ ⟶ (copower U W').obj Δ :=
  Functor.indexedCoprod.homApp U f Δ

/-- The raw components induced by a truncated simplicial-object morphism form a natural
family. -/
@[stacks 017E "truncated copower induced naturality"]
theorem copower.homApp.naturality
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') {Δ₁ Δ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    (copower U W).map σ ≫ copower.homApp U f Δ₂ =
      copower.homApp U f Δ₁ ≫ (copower U W').map σ := sorry

/-- The morphism of truncated simplicial copowers induced by a morphism in the truncated
simplicial-object variable. -/
@[stacks 017E "truncated copower morphism in the object variable"]
abbrev copower.hom
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') : copower U W ⟶ copower U W' :=
  Functor.indexedCoprod.hom U f

/-- A component of `Truncated.copower.hom` is its corresponding raw component. -/
@[simp, stacks 017E "truncated copower induced component formula"]
theorem copower.hom_app
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (copower.hom U f).app Δ = copower.homApp U f Δ := sorry

/-- Computing `Truncated.copower.hom` after a coproduct injection. -/
@[simp, stacks 017E "truncated copower induced injection formula"]
theorem copower.hom.ι
    [HasCopower U W] [HasCopower U W']
    (f : W ⟶ W') (Δ : (SimplexCategory.Truncated n)ᵒᵖ) (u : U.obj Δ) :
    Sigma.ι (fun _ : U.obj Δ ↦ W.obj Δ) u ≫ (copower.hom U f).app Δ =
      f.app Δ ≫ Sigma.ι (fun _ : U.obj Δ ↦ W'.obj Δ) u := sorry

/-- Identity law for `Truncated.copower.hom`. -/
@[simp, stacks 017E "truncated copower induced identity"]
theorem copower.hom.id
    (W : SimplicialObject.Truncated C n)
    [HasCopower U W] :
    copower.hom U (𝟙 W) = 𝟙 (copower U W) := sorry

/-- Composition law for `Truncated.copower.hom`. -/
@[stacks 017E "truncated copower induced composition"]
theorem copower.hom.comp
    {W₁ W₂ W₃ : SimplicialObject.Truncated C n}
    [HasCopower U W₁] [HasCopower U W₂] [HasCopower U W₃]
    (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) :
    copower.hom U (f ≫ g) = copower.hom U f ≫ copower.hom U g := sorry

end ObjectVariable

section ObjectVariableFunctor

variable (U : SSet.Truncated.{w} n)
variable [HasCopowers U C]

/-- The functor in the truncated simplicial-object variable induced by a fixed indexing
truncated simplicial set. -/
@[stacks 017E "truncated copower functor in the object variable"]
abbrev copower.functor : SimplicialObject.Truncated C n ⥤ SimplicialObject.Truncated C n :=
  Functor.indexedCoprod.functor U

end ObjectVariableFunctor

section IndexVariable

variable {U V : SSet.Truncated.{w} n}
variable (X : SimplicialObject.Truncated C n)

/-- The raw component induced on truncated copowers by a morphism of indexing truncated
simplicial sets. -/
@[stacks 017E "truncated copower index-map component"]
abbrev copower.indexHomApp
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (copower U X).obj Δ ⟶ (copower V X).obj Δ :=
  Functor.indexedCoprod.indexHomApp X a Δ

/-- The raw components induced by truncated reindexing form a natural family. -/
@[stacks 017E "truncated copower index-map naturality"]
theorem copower.indexHomApp.naturality
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) {Δ₁ Δ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    (copower U X).map σ ≫ copower.indexHomApp X a Δ₂ =
      copower.indexHomApp X a Δ₁ ≫ (copower V X).map σ := sorry

/-- The morphism of truncated copowers induced by a morphism of indexing truncated simplicial
sets. -/
@[stacks 017E "truncated copower morphism in the indexing variable"]
abbrev copower.indexHom
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) : copower U X ⟶ copower V X :=
  Functor.indexedCoprod.indexHom X a

/-- A component of `Truncated.copower.indexHom` is its corresponding raw component. -/
@[simp, stacks 017E "truncated copower index-map component formula"]
theorem copower.indexHom_app
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (copower.indexHom X a).app Δ = copower.indexHomApp X a Δ := sorry

/-- Computing `Truncated.copower.indexHom` after a coproduct injection. -/
@[simp, stacks 017E "truncated copower index-map injection formula"]
theorem copower.indexHom.ι
    [HasCopower U X] [HasCopower V X]
    (a : U ⟶ V) (Δ : (SimplexCategory.Truncated n)ᵒᵖ) (u : U.obj Δ) :
    Sigma.ι (fun _ : U.obj Δ ↦ X.obj Δ) u ≫ (copower.indexHom X a).app Δ =
      Sigma.ι (fun _ : V.obj Δ ↦ X.obj Δ) (a.app Δ u) := sorry

/-- Identity law for `Truncated.copower.indexHom`. -/
@[simp, stacks 017E "truncated copower index-map identity"]
theorem copower.indexHom.id
    (U : SSet.Truncated.{w} n)
    [HasCopower U X] :
    copower.indexHom X (𝟙 U) = 𝟙 (copower U X) := sorry

/-- Composition law for `Truncated.copower.indexHom`. -/
@[stacks 017E "truncated copower index-map composition"]
theorem copower.indexHom.comp
    {U₁ U₂ U₃ : SSet.Truncated.{w} n}
    [HasCopower U₁ X] [HasCopower U₂ X] [HasCopower U₃ X]
    (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) :
    copower.indexHom X (a ≫ b) = copower.indexHom X a ≫ copower.indexHom X b := sorry

end IndexVariable

section IndexVariableFunctor

variable (X : SimplicialObject.Truncated C n)
variable [X.HasCopowersOf]

/-- The functor in the indexing truncated simplicial set for a fixed truncated simplicial
object. -/
@[stacks 017E "truncated copower functor in the indexing variable"]
abbrev copower.indexFunctor : SSet.Truncated.{w} n ⥤ SimplicialObject.Truncated C n :=
  Functor.indexedCoprod.indexFunctor X

end IndexVariableFunctor

section MixedVariable

variable {U V : SSet.Truncated.{w} n}
variable {X Y : SimplicialObject.Truncated C n}

/-- Reindexing a truncated copower is natural in the truncated simplicial-object variable. -/
@[stacks 017E "truncated copower variable interchange"]
theorem copower.indexHom.naturality
    [HasCopower U X] [HasCopower U Y] [HasCopower V X] [HasCopower V Y]
    (a : U ⟶ V) (f : X ⟶ Y) :
    CommSq (copower.hom U f) (copower.indexHom X a)
      (copower.indexHom Y a) (copower.hom V f) := sorry

end MixedVariable

section IndexNaturalTransformation

variable {U V : SSet.Truncated.{w} n}
variable [HasCopowers U C] [HasCopowers V C]

/-- A map of truncated indexing simplicial sets induces a natural transformation between the
corresponding fixed-index copower functors. -/
@[stacks 017E "truncated copower functoriality in the indexing variable"]
abbrev copower.indexHom.natTrans (a : U ⟶ V) :
    copower.functor (C := C) U ⟶ copower.functor (C := C) V :=
  Functor.indexedCoprod.indexHom.natTrans (C := C) a

/-- The component of the natural transformation induced by a truncated indexing map. -/
@[simp, stacks 017E "truncated copower index natural-transformation component"]
theorem copower.indexHom.natTrans.app
    (a : U ⟶ V) (X : SimplicialObject.Truncated C n) :
    (copower.indexHom.natTrans (C := C) a).app X = copower.indexHom X a := sorry

/-- The truncated copower index natural transformation associated to an identity is the
identity. -/
@[simp, stacks 017E "truncated copower index natural-transformation identity"]
theorem copower.indexHom.natTrans.id
    (U : SSet.Truncated.{w} n) [HasCopowers U C] :
    copower.indexHom.natTrans (C := C) (𝟙 U) =
      𝟙 (copower.functor (C := C) U) := sorry

/-- Truncated copower index natural transformations preserve composition. -/
@[stacks 017E "truncated copower index natural-transformation composition"]
theorem copower.indexHom.natTrans.comp {U V W : SSet.Truncated.{w} n}
    [HasCopowers U C] [HasCopowers V C] [HasCopowers W C]
    (a : U ⟶ V) (b : V ⟶ W) :
    copower.indexHom.natTrans (C := C) (a ≫ b) =
      copower.indexHom.natTrans (C := C) a ≫
        copower.indexHom.natTrans (C := C) b := sorry

end IndexNaturalTransformation

/-- `HasCopowers.OfIndex K C` records truncated copowers by every indexing object in the image
of `K`, uniformly in the truncated simplicial-object variable. -/
@[stacks 017E "truncated copowers along an indexing functor"]
abbrev HasCopowers.OfIndex {D : Type d} [Category.{e} D]
    (K : D ⥤ SSet.Truncated.{w} n) (C : Type u) [Category.{v} C] : Prop :=
  Functor.HasIndexedCoprods.OfIndex K C

namespace HasCopowers.OfIndex

/-- Categories with all `w`-small coproducts admit truncated copowers along every indexing
functor. -/
@[stacks 017E "indexed truncated simplicial copowers from coproducts"]
instance ofCoproducts {D : Type d} [Category.{e} D] [HasCoproducts.{w} C]
    (K : D ⥤ SSet.Truncated.{w} n) : HasCopowers.OfIndex K C := sorry

end HasCopowers.OfIndex

section Bifunctor

variable {D : Type d} [Category.{e} D]
variable (K : D ⥤ SSet.Truncated.{w} n)
variable [HasCopowers.OfIndex K C]

/-- Identity law for truncated index-variable natural transformations along an indexing
functor. -/
@[stacks 017E "indexed truncated copower functor identity"]
theorem copower.ofIndex.map.id (d : D) :
    copower.indexHom.natTrans (C := C) (K.map (𝟙 d)) =
      𝟙 (copower.functor (C := C) (K.obj d)) := sorry

/-- Composition law for truncated index-variable natural transformations along an indexing
functor. -/
@[stacks 017E "indexed truncated copower functor composition"]
theorem copower.ofIndex.map.comp {d₁ d₂ d₃ : D} (f : d₁ ⟶ d₂) (g : d₂ ⟶ d₃) :
    copower.indexHom.natTrans (C := C) (K.map (f ≫ g)) =
      copower.indexHom.natTrans (C := C) (K.map f) ≫
        copower.indexHom.natTrans (C := C) (K.map g) := sorry

/-- Truncated copower as a curried bifunctor after restricting the indexing objects along `K`. -/
@[stacks 017E "curried truncated simplicial copower bifunctor"]
abbrev copower.ofIndex :
    D ⥤ SimplicialObject.Truncated C n ⥤ SimplicialObject.Truncated C n :=
  Functor.indexedCoprod.bifunctor (C := C) K

/-- Evaluating a truncated indexed copower bifunctor on both variables gives the corresponding
copower. -/
@[simp, stacks 017E "indexed truncated copower object formula"]
theorem copower.ofIndex.obj (d : D) (X : SimplicialObject.Truncated C n) :
    ((copower.ofIndex K).obj d).obj X = copower (K.obj d) X := sorry

/-- The action of a truncated indexed copower bifunctor in the object variable. -/
@[simp, stacks 017E "indexed truncated copower object-variable map formula"]
theorem copower.ofIndex.obj.map
    (d : D) {X Y : SimplicialObject.Truncated C n} (f : X ⟶ Y) :
    ((copower.ofIndex K).obj d).map f = copower.hom (K.obj d) f := sorry

/-- The component of a truncated indexed copower bifunctor in the indexing variable. -/
@[simp, stacks 017E "indexed truncated copower map formula"]
theorem copower.ofIndex.map.app {d d' : D} (f : d ⟶ d')
    (X : SimplicialObject.Truncated C n) :
    ((copower.ofIndex K).map f).app X = copower.indexHom X (K.map f) := sorry

end Bifunctor

section GlobalBifunctor

variable [HasCopowers.OfIndex (𝟭 (SSet.Truncated.{w} n)) C]

/-- Truncated copower as a bifunctor in arbitrary truncated simplicial sets and objects. -/
@[stacks 017E "truncated simplicial copower bifunctor"]
abbrev copower.bifunctor :
    SSet.Truncated.{w} n ⥤
      SimplicialObject.Truncated C n ⥤ SimplicialObject.Truncated C n :=
  copower.ofIndex (C := C) (𝟭 (SSet.Truncated.{w} n))

/-- Evaluating the truncated copower bifunctor gives the corresponding copower. -/
@[simp, stacks 017E "truncated copower bifunctor object formula"]
theorem copower.bifunctor.obj
    (U : SSet.Truncated.{w} n) (X : SimplicialObject.Truncated C n) :
    ((copower.bifunctor (C := C) (n := n)).obj U).obj X = copower U X := sorry

/-- The action of the truncated copower bifunctor in the object variable. -/
@[simp, stacks 017E "truncated copower bifunctor object-variable map formula"]
theorem copower.bifunctor.obj.map
    (U : SSet.Truncated.{w} n) {X Y : SimplicialObject.Truncated C n} (f : X ⟶ Y) :
    ((copower.bifunctor (C := C) (n := n)).obj U).map f = copower.hom U f := sorry

/-- The component of the truncated copower bifunctor in its indexing variable. -/
@[simp, stacks 017E "truncated copower bifunctor index-map formula"]
theorem copower.bifunctor.map.app {U V : SSet.Truncated.{w} n} (a : U ⟶ V)
    (X : SimplicialObject.Truncated C n) :
    ((copower.bifunctor (C := C) (n := n)).map a).app X = copower.indexHom X a := sorry

end GlobalBifunctor

end CategoryTheory.SimplicialObject.Truncated
