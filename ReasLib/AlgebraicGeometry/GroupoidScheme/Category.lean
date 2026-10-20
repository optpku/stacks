module

public import ReasLib.AlgebraicGeometry.GroupoidScheme

/-!
# The category of groupoid schemes over a fixed scheme

This module packages the explicit identity and composition operations on morphisms of
groupoid schemes as a bundled category, without installing a category instance on the raw
type of groupoid schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

namespace Hom

/-- Morphisms of groupoid schemes are equal when their object and arrow components agree. -/
theorem ext {S : Scheme.{u}} {G H : GroupoidScheme S} {f g : Hom G H}
    (h_obj : f.obj = g.obj) (h_arrow : f.arrow = g.arrow) : f = g := sorry

attribute [ext] AlgebraicGeometry.GroupoidScheme.Hom.ext

/-- Composing an identity morphism on the left does not change a groupoid-scheme morphism. -/
theorem id_comp {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    comp (id G) f = f := sorry

/-- Composing an identity morphism on the right does not change a groupoid-scheme morphism. -/
theorem comp_id {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) :
    comp f (id H) = f := sorry

/-- Composition of groupoid-scheme morphisms is associative. -/
theorem assoc {S : Scheme.{u}} {G H K L : GroupoidScheme S}
    (f : Hom G H) (g : Hom H K) (h : Hom K L) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- The explicit category structure on groupoid schemes over `S`. -/
@[reducible] def categoryStruct (S : Scheme.{u}) : Category (GroupoidScheme S) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The bundled category of groupoid schemes over `S`. -/
def category (S : Scheme.{u}) : Cat :=
  @Cat.of (GroupoidScheme S) (categoryStruct S)

/-- The bundled category of groupoid schemes equipped with a morphism to `G`. -/
@[reducible] def overCategory {S : Scheme.{u}} (G : GroupoidScheme S) : Cat :=
  let G' : category S := G
  Cat.of (Over G')

end AlgebraicGeometry.GroupoidScheme
