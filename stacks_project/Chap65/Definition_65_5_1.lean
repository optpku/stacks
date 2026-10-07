module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 65.5.1: for a scheme `S` and a representable morphism `a : F ⟶ G` of
presheaves `F, G : (Over S)ᵒᵖ ⥤ Type u` on `(Sch/S)_fppf`, and for a property `P` of
scheme morphisms that is stable under base change and fppf local on the base, `a`
has property `P` iff every represented pullback `V_ξ ⟶ U` has `P`. This is the
canonical predicate `(MorphismProperty.over P).presheaf`. The stability and fppf
locality hypotheses on `P` are standing usage restrictions, not extra definitional
content. -/
@[stacks 025V] #check (AlgebraicGeometry.Scheme.representableMorphismProperty :
  (S : Scheme.{u}) → MorphismProperty Scheme.{u} → MorphismProperty ((Over S)ᵒᵖ ⥤ Type u))

section

variable (S : Scheme.{u}) (P : MorphismProperty Scheme.{u})
variable (F G : (Over S)ᵒᵖ ⥤ Type u) (a : F ⟶ G)
variable (ha : yoneda.relativelyRepresentable a)
variable (U : Over S) (ξ : yoneda.obj U ⟶ G)

open Functor.relativelyRepresentable

#check (MorphismProperty.over P).presheaf a
#check yoneda.relativelyRepresentable a
#check ha.pullback ξ
#check ha.snd ξ
#check MorphismProperty.relative.property_snd
#check MorphismProperty.relative_of_snd
#check P.IsStableUnderBaseChange
#check P.IsLocalAtTarget Scheme.fppfPrecoverage

end
