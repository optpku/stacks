module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Over
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.Gluing.MorphismProperties
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

/-!
# Flat schemes and pushout gluing

Pushout gluing restricts to an adjoint equivalence between schemes flat over
the pushout and compatible gluing triples whose two components are flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Pushout.Gluing

variable {X X' Y : Scheme.{u}}
variable (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [IsAffineHom f]

/-- On a scheme flat over `pushout i f`, the counit from gluing its two base changes back to
the original scheme is an isomorphism. -/
theorem counitIsIsoOfFlat (Z : Over (pushout i f)) [AlgebraicGeometry.Flat Z.hom] :
    IsIso ((Gluing.adjunction i f).counit.app Z) := sorry

namespace Flat

/-- The object property of a compatible gluing triple whose two components are flat. -/
def tripleProperty :
    ObjectProperty (CategoricalPullback (Over.pullback f) (Over.pullback i)) :=
  fun P ↦ AlgebraicGeometry.Flat P.fst.hom ∧ AlgebraicGeometry.Flat P.snd.hom

/-- A compatible triple satisfies `tripleProperty i f` exactly when both structure morphisms
are flat. -/
theorem tripleProperty_iff
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    tripleProperty i f P ↔
      AlgebraicGeometry.Flat P.fst.hom ∧ AlgebraicGeometry.Flat P.snd.hom := sorry

/-- The category of compatible gluing triples with both components flat. -/
abbrev Triple := (tripleProperty i f).FullSubcategory

/-- The first component of a componentwise-flat gluing triple is flat. -/
theorem instFstFlat (P : Triple i f) : Flat ((P.obj.fst).hom) :=
  P.property.1

/-- The second component of a componentwise-flat gluing triple is flat. -/
theorem instSndFlat (P : Triple i f) : Flat ((P.obj.snd).hom) :=
  P.property.2

/-- Base change of a flat scheme over the pushout gives a componentwise-flat gluing triple. -/
theorem baseChange_mem (Z : Over (pushout i f)) (hZ : flatOverProperty (pushout i f) Z) :
    tripleProperty i f ((Gluing.baseChange i f).obj Z) := sorry

/-- Base change restricted to flat schemes over the pushout and componentwise-flat triples. -/
def baseChange : FlatOver (pushout i f) ⥤ Triple i f :=
  ObjectProperty.FullSubcategory.restrict (Gluing.baseChange i f) (baseChange_mem i f)

/-- The underlying triple of restricted base change is the ordinary gluing base change. -/
theorem baseChange_obj (Z : FlatOver (pushout i f)) :
    ((Flat.baseChange i f).obj Z).obj = (Gluing.baseChange i f).obj Z.obj := sorry

/-- Pushout gluing of a componentwise-flat triple is flat over the pushout. -/
theorem glue_mem
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i))
    (hP : tripleProperty i f P) :
    flatOverProperty (pushout i f) ((Gluing.glue i f).obj P) := sorry

/-- Pushout gluing restricted to componentwise-flat triples and flat schemes over the pushout. -/
def glue : Triple i f ⥤ FlatOver (pushout i f) :=
  ObjectProperty.FullSubcategory.restrict (Gluing.glue i f) (glue_mem i f)

/-- The underlying scheme over the pushout of restricted gluing is ordinary pushout gluing. -/
theorem glue_obj (P : Triple i f) :
    ((Flat.glue i f).obj P).obj = (Gluing.glue i f).obj P.obj := sorry

/-- The gluing adjunction restricted to componentwise-flat triples and flat schemes over the
pushout. -/
noncomputable def adjunction : Flat.glue i f ⊣ Flat.baseChange i f :=
  ObjectProperty.FullSubcategory.adjunction (Gluing.glue i f) (Gluing.baseChange i f)
    (Gluing.adjunction i f) (glue_mem i f) (baseChange_mem i f)

/-- Every component of the unit of the restricted flat gluing adjunction is an isomorphism. -/
theorem unitAppIsIso (P : Triple i f) : IsIso ((Flat.adjunction i f).unit.app P) := sorry

/-- Every component of the counit of the restricted flat gluing adjunction is an isomorphism. -/
theorem counitAppIsIso (Z : FlatOver (pushout i f)) :
    IsIso ((Flat.adjunction i f).counit.app Z) := sorry

/-- Base change is an equivalence from schemes flat over the pushout to compatible triples
whose two components are flat, with specified quasi-inverse `Flat.glue i f`. -/
theorem baseChangeIsEquivalence : Functor.IsEquivalence (Flat.baseChange i f) := sorry

/-- Restricted pushout gluing is the quasi-inverse equivalence to restricted base change. -/
theorem glueIsEquivalence : Functor.IsEquivalence (Flat.glue i f) := sorry

end Flat

end AlgebraicGeometry.Scheme.Pushout.Gluing
