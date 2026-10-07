module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import stacks_project.Chap81.Lemma_81_6_7_MorphismProperties
public import stacks_project.Chap81.Lemma_81_6_7_Over

/-!
# Flat algebraic spaces and pushout gluing

Pushout gluing restricts to an adjoint equivalence between algebraic spaces
flat over the pushout and compatible gluing triples whose two components are
flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing

variable {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
variable (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]

/-- On an algebraic space flat over `pushout i f`, the counit from gluing its two
base changes back to the original algebraic space is an isomorphism. -/
instance counitIsIsoOfFlat (Z : Over (pushout i f)) [Flat Z.hom] :
    IsIso ((Gluing.adjunction i f).counit.app Z) :=
  sorry

namespace Flat

/-- The object property of a compatible gluing triple whose two components are
flat. -/
def tripleProperty :
    ObjectProperty (CategoricalPullback (Over.pullback f) (Over.pullback i)) :=
  fun P ↦ (AlgebraicGeometry.AlgebraicSpace.Flat P.fst.hom ∧
    AlgebraicGeometry.AlgebraicSpace.Flat P.snd.hom)

/-- A compatible triple satisfies `tripleProperty i f` exactly when both
structure morphisms are flat. -/
theorem tripleProperty_iff
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    tripleProperty i f P ↔
      AlgebraicGeometry.AlgebraicSpace.Flat P.fst.hom ∧
        AlgebraicGeometry.AlgebraicSpace.Flat P.snd.hom :=
  sorry

/-- The category of compatible gluing triples with both components flat. -/
abbrev Triple := (tripleProperty i f).FullSubcategory

/-- The first component of a componentwise-flat gluing triple is flat. -/
instance instFstFlat (P : Triple i f) :
    AlgebraicGeometry.AlgebraicSpace.Flat P.obj.fst.hom :=
  P.property.1

/-- The second component of a componentwise-flat gluing triple is flat. -/
instance instSndFlat (P : Triple i f) :
    AlgebraicGeometry.AlgebraicSpace.Flat P.obj.snd.hom :=
  P.property.2

/-- Base change of a flat algebraic space over the pushout gives a
componentwise-flat gluing triple. -/
theorem baseChange_mem (Z : Over (pushout i f))
    (hZ : flatOverProperty (pushout i f) Z) :
    tripleProperty i f ((Gluing.baseChange i f).obj Z) :=
  sorry

/-- Base change restricted to flat algebraic spaces over the pushout and
componentwise-flat triples. -/
def baseChange : FlatOver (pushout i f) ⥤ Triple i f :=
  ObjectProperty.FullSubcategory.restrict (Gluing.baseChange i f)
    (baseChange_mem i f)

/-- The underlying triple of restricted base change is the ordinary gluing
base change. -/
theorem baseChange_obj (Z : FlatOver (pushout i f)) :
    ((Flat.baseChange i f).obj Z).obj = (Gluing.baseChange i f).obj Z.obj :=
  sorry

/-- Pushout gluing of a componentwise-flat triple is flat over the pushout. -/
theorem glue_mem (P : CategoricalPullback (Over.pullback f) (Over.pullback i))
    (hP : tripleProperty i f P) :
    flatOverProperty (pushout i f) ((Gluing.glue i f).obj P) :=
  sorry

/-- Pushout gluing restricted to componentwise-flat triples and flat algebraic
spaces over the pushout. -/
def glue : Triple i f ⥤ FlatOver (pushout i f) :=
  ObjectProperty.FullSubcategory.restrict (Gluing.glue i f) (glue_mem i f)

/-- The underlying algebraic space over the pushout of restricted gluing is
ordinary pushout gluing. -/
theorem glue_obj (P : Triple i f) :
    ((Flat.glue i f).obj P).obj = (Gluing.glue i f).obj P.obj :=
  sorry

/-- The gluing adjunction restricted to componentwise-flat triples and flat
algebraic spaces over the pushout. -/
noncomputable def adjunction : Flat.glue i f ⊣ Flat.baseChange i f :=
  ObjectProperty.FullSubcategory.adjunction (Gluing.glue i f)
    (Gluing.baseChange i f) (Gluing.adjunction i f) (glue_mem i f)
    (baseChange_mem i f)

/-- Every component of the unit of the restricted flat gluing adjunction is an
isomorphism. -/
instance unitAppIsIso (P : Triple i f) :
    IsIso ((Flat.adjunction i f).unit.app P) :=
  sorry

/-- Every component of the counit of the restricted flat gluing adjunction is an
isomorphism. -/
instance counitAppIsIso (Z : FlatOver (pushout i f)) :
    IsIso ((Flat.adjunction i f).counit.app Z) :=
  sorry

/-- Base change is an equivalence from algebraic spaces flat over the pushout to
compatible triples whose two components are flat, with specified quasi-inverse
`Flat.glue i f`. -/
instance baseChangeIsEquivalence :
    Functor.IsEquivalence (Flat.baseChange i f) :=
  sorry

/-- Restricted pushout gluing is the quasi-inverse equivalence to restricted
base change. -/
instance glueIsEquivalence : Functor.IsEquivalence (Flat.glue i f) :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing
