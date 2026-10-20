module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Locally quasi-finite morphisms of algebraic spaces

This module preserves the source-facing import surface for existing users
while exposing the canonical shared locally quasi-finite API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite -/
#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

/- AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_iff -/
#check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    LocallyQuasiFinite f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyQuasiFinite h.left)

/- AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.spec -/
#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [LocallyQuasiFinite f] →
      ∀ {U V : Over S}
        (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyQuasiFinite h.left)

/- AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.id -/
#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, LocallyQuasiFinite (𝟙 X))

/- AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.of_presheaf -/
#check (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.of_presheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
    (over
        (@AlgebraicGeometry.LocallyQuasiFinite :
          MorphismProperty Scheme.{u})).presheaf f →
      LocallyQuasiFinite f)

end AlgebraicGeometry.AlgebraicSpace
