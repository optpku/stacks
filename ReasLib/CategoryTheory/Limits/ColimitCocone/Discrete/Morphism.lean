module

public import ReasLib.CategoryTheory.Limits.ColimitCocone.Morphism
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Morphisms between Explicit Colimits of Discrete Families

For discrete diagrams, a family of component maps is already a natural transformation. This
leaf packages that conversion once and exposes the induced map between arbitrary explicit
coproduct cocones, independently of the indexing type.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u u'

namespace CategoryTheory.Limits.ColimitCocone.Discrete

variable {I : Type u}
variable {C : Type u'} [Category.{v} C]

/-- The map between explicit colimits of two discrete families induced by component maps. -/
def map {F G : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (f : ∀ i : I, F i ⟶ G i) : P.cocone.pt ⟶ Q.cocone.pt :=
  ColimitCocone.map P Q (CategoryTheory.Discrete.natTrans fun i ↦ f i.as)

/-- A map between explicit colimits of discrete families has the prescribed composite with each
source leg. -/
@[reassoc (attr := simp)]
theorem ι_map {F G : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (f : ∀ i : I, F i ⟶ G i) (i : I) :
    P.cocone.ι.app ⟨i⟩ ≫ map P Q f = f i ≫ Q.cocone.ι.app ⟨i⟩ := sorry

/-- Morphisms out of an explicit colimit of a discrete family are determined on the family
legs. -/
@[ext]
theorem hom_ext {F : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F)) {X : C}
    {f g : P.cocone.pt ⟶ X}
    (h : ∀ i : I, P.cocone.ι.app ⟨i⟩ ≫ f = P.cocone.ι.app ⟨i⟩ ≫ g) :
    f = g := sorry

/-- The map of explicit colimits induced by identity component maps is the identity. -/
@[simp]
theorem map_id {F : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F)) :
    map P P (fun i ↦ 𝟙 (F i)) = 𝟙 P.cocone.pt := sorry

/-- Maps between explicit colimits of discrete families respect componentwise composition. -/
@[reassoc]
theorem map_comp {F G H : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (R : ColimitCocone (CategoryTheory.Discrete.functor H))
    (f : ∀ i : I, F i ⟶ G i) (g : ∀ i : I, G i ⟶ H i) :
    map P Q f ≫ map Q R g = map P R (fun i ↦ f i ≫ g i) := sorry

/-- On coproduct cocones selected by `HasCoproduct` instances, the explicit discrete-family map
is Mathlib's `Sigma.map`. -/
@[simp]
theorem map_getColimitCocone {F G : I → C} [HasCoproduct F] [HasCoproduct G]
    (f : ∀ i : I, F i ⟶ G i) :
    map (getColimitCocone (CategoryTheory.Discrete.functor F))
      (getColimitCocone (CategoryTheory.Discrete.functor G)) f = Sigma.map f := sorry

end CategoryTheory.Limits.ColimitCocone.Discrete
