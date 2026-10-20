module

public import ReasLib.AlgebraicGeometry.FormalScheme.Scheme
public import stacks_project.Chap87.«87_2_0_2_LocallyTopologicallyRingedSpace»

/-!
# Legacy views of locally topologically ringed spaces

The views below repackage the supplied sheaf and locality proofs in the record presentation
of locally topologically ringed spaces. They do not select objects or morphisms.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpaceCat

/-- Repackage the supplied sheaf and local ring stalks in the record presentation. -/
def toLegacy (X : LocallyTopologicallyRingedSpaceCat.{u}) :
    LocallyTopologicallyRingedSpace.{u} where
  toSheafedSpace := X.toSheafedSpace
  isLocalRing := X.property

/-- The record view retains the supplied sheafed space. -/
theorem toLegacy_toSheafedSpace (X : LocallyTopologicallyRingedSpaceCat.{u}) :
    X.toLegacy.toSheafedSpace = X.toSheafedSpace := rfl

/-- The record view retains the supplied topological space. -/
theorem toLegacy_carrier (X : LocallyTopologicallyRingedSpaceCat.{u}) :
    X.toLegacy.carrier = X.carrier := rfl

/-- The record view retains the supplied presheaf. -/
theorem toLegacy_presheaf (X : LocallyTopologicallyRingedSpaceCat.{u}) :
    X.toLegacy.presheaf = X.toSheafedSpace.presheaf := rfl

/-- The record view retains the supplied local-ring proof at every stalk. -/
theorem toLegacy_isLocalRing (X : LocallyTopologicallyRingedSpaceCat.{u}) (x : X.carrier) :
    X.toLegacy.isLocalRing x = X.property x := rfl

/-- Coercion to the record presentation only repackages supplied fields. -/
instance instCoeLegacy :
    Coe LocallyTopologicallyRingedSpaceCat.{u} LocallyTopologicallyRingedSpace.{u} where
  coe := toLegacy

/-- Repackage the supplied sheaf morphism and locality proofs in the record presentation. -/
def Hom.toLegacy {X Y : LocallyTopologicallyRingedSpaceCat.{u}} (f : Hom X Y) :
    LocallyTopologicallyRingedSpace.Hom X.toLegacy Y.toLegacy where
  toSheafedHom := f.toSheafedHom
  isLocalHom := f.property

/-- The record morphism view retains the supplied sheafed-space morphism. -/
theorem Hom.toLegacy_toSheafedHom {X Y : LocallyTopologicallyRingedSpaceCat.{u}} (f : Hom X Y) :
    f.toLegacy.toSheafedHom = f.toSheafedHom := rfl

/-- The record morphism view retains the supplied stalk-locality proofs. -/
theorem Hom.toLegacy_isLocalHom {X Y : LocallyTopologicallyRingedSpaceCat.{u}}
    (f : Hom X Y) (x : X.carrier) : f.toLegacy.isLocalHom x = f.property x := rfl

/-- Coercion of morphisms to record views only repackages supplied fields. -/
instance instCoeHomLegacy (X Y : LocallyTopologicallyRingedSpaceCat.{u}) :
    Coe (Hom X Y) (LocallyTopologicallyRingedSpace.Hom X.toLegacy Y.toLegacy) where
  coe := Hom.toLegacy

/-- The identity morphism retains its identity under the record view. -/
theorem id_toLegacy (X : LocallyTopologicallyRingedSpaceCat.{u}) :
    (id X).toLegacy = LocallyTopologicallyRingedSpace.id X.toLegacy := rfl

/-- Composition of supplied morphisms commutes with taking record views. -/
theorem comp_toLegacy {X Y Z : LocallyTopologicallyRingedSpaceCat.{u}}
    (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).toLegacy = LocallyTopologicallyRingedSpace.comp f.toLegacy g.toLegacy := rfl

end AlgebraicGeometry.LocallyTopologicallyRingedSpaceCat
