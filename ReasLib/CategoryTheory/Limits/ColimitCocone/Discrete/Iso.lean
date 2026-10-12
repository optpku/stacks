/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.ColimitCocone.Discrete.Morphism
public import ReasLib.CategoryTheory.Limits.ColimitCocone.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms between Explicit Colimits of Discrete Families

This leaf turns a family of component isomorphisms into the induced isomorphism between any
explicit colimits of the corresponding discrete diagrams. It is the coproduct-facing adapter to
the shape-independent `ColimitCocone.mapIso` API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u u'

namespace CategoryTheory.Limits.ColimitCocone.Discrete

variable {I : Type u}
variable {C : Type u'} [Category.{v} C]

/-- The isomorphism between explicit colimits of two discrete families induced componentwise. -/
@[stacks 002F "explicit coproduct cocone isomorphism"]
def mapIso {F G : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (e : ∀ i : I, F i ≅ G i) : P.cocone.pt ≅ Q.cocone.pt :=
  ColimitCocone.mapIso P Q (CategoryTheory.Discrete.natIso fun i ↦ e i.as)

/-- The forward morphism of the discrete-family `mapIso` is induced by the component homs. -/
@[simp]
theorem mapIso_hom {F G : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (e : ∀ i : I, F i ≅ G i) :
    (mapIso P Q e).hom = map P Q (fun i ↦ (e i).hom) := sorry

/-- The inverse morphism of the discrete-family `mapIso` is induced by the component inverses. -/
@[simp]
theorem mapIso_inv {F G : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (e : ∀ i : I, F i ≅ G i) :
    (mapIso P Q e).inv = map Q P (fun i ↦ (e i).inv) := sorry

/-- The forward discrete-family isomorphism has the expected composite with every source leg. -/
@[reassoc (attr := simp)]
theorem ι_mapIso_hom {F G : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (e : ∀ i : I, F i ≅ G i) (i : I) :
    P.cocone.ι.app ⟨i⟩ ≫ (mapIso P Q e).hom =
      (e i).hom ≫ Q.cocone.ι.app ⟨i⟩ := sorry

/-- The inverse discrete-family isomorphism has the expected composite with every target leg. -/
@[reassoc (attr := simp)]
theorem ι_mapIso_inv {F G : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (e : ∀ i : I, F i ≅ G i) (i : I) :
    Q.cocone.ι.app ⟨i⟩ ≫ (mapIso P Q e).inv =
      (e i).inv ≫ P.cocone.ι.app ⟨i⟩ := sorry

/-- On coproduct cocones selected by the two `HasCoproduct` instances, the explicit
discrete-family isomorphism is the canonical colimit isomorphism of the componentwise
natural isomorphism. -/
@[simp]
theorem mapIso_getColimitCocone {F G : I → C} [HasCoproduct F] [HasCoproduct G]
    (e : ∀ i : I, F i ≅ G i) :
    mapIso (getColimitCocone (CategoryTheory.Discrete.functor F))
      (getColimitCocone (CategoryTheory.Discrete.functor G)) e =
        HasColimit.isoOfNatIso (CategoryTheory.Discrete.natIso fun i ↦ e i.as) := sorry

/-- Identity component isomorphisms induce the identity isomorphism of an explicit coproduct
cocone point. -/
@[simp]
theorem mapIso_refl {F : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F)) :
    mapIso P P (fun i ↦ Iso.refl (F i)) = Iso.refl P.cocone.pt := sorry

/-- Componentwise symmetry reverses the induced isomorphism of explicit coproduct cocones. -/
@[simp]
theorem mapIso_symm {F G : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (e : ∀ i : I, F i ≅ G i) :
    (mapIso P Q e).symm = mapIso Q P (fun i ↦ (e i).symm) := sorry

/-- Componentwise transitivity agrees with composition of the induced explicit-coproduct
isomorphisms. -/
theorem mapIso_trans {F G H : I → C}
    (P : ColimitCocone (CategoryTheory.Discrete.functor F))
    (Q : ColimitCocone (CategoryTheory.Discrete.functor G))
    (R : ColimitCocone (CategoryTheory.Discrete.functor H))
    (e : ∀ i : I, F i ≅ G i) (e' : ∀ i : I, G i ≅ H i) :
    mapIso P Q e ≪≫ mapIso Q R e' = mapIso P R (fun i ↦ e i ≪≫ e' i) := sorry

end CategoryTheory.Limits.ColimitCocone.Discrete
