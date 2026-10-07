module

public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.AlgebraicGeometry.Scheme.Cone.Basic

/-!
# Explicit category operations for cones

This file supplies named identity and composition operations for cones over a fixed scheme and
packages them as an explicit category value.  It does not register a category instance.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

namespace ConeHom

/-- The identity scheme morphism of a cone lies over the base. -/
theorem idOverBase (X : ConeOver S) :
    (𝟙 X.C) ≫ X.π = X.π := sorry

end ConeHom

namespace ConeOver

/-- Transporting the identity pullback through the chosen algebra identification gives the
identity chosen-algebra morphism. -/
theorem chosenAlgebraPullback_id (X : ConeOver S) :
    chosenAlgebraPullback S (𝟙 X.C) (ConeHom.idOverBase S X) =
      𝟙 X.pushforwardGrading.algebra := sorry

end ConeOver


namespace ConeHom

/-- The identity scheme morphism is compatible with the explicit grading. -/
theorem idCompatibleWithGrading (X : ConeOver S) :
    coneHomCompatibleWithGrading S (𝟙 X.C) (idOverBase S X) := sorry

/-- The identity morphism of a cone. -/
def id (X : ConeOver S) : ConeHom S X X where
  hom := 𝟙 X.C
  overBase := idOverBase S X
  compatibleWithGrading := idCompatibleWithGrading S X

/-- The composite of two underlying scheme morphisms lies over the base. -/
theorem compOverBase {X Y Z : ConeOver S}
    (f : ConeHom S X Y) (g : ConeHom S Y Z) :
    (f.hom ≫ g.hom) ≫ Z.π = X.π := sorry

end ConeHom

namespace ConeOver

/-- Pullback on chosen algebras reverses composition of cone maps. -/
theorem chosenAlgebraPullback_comp {X Y Z : ConeOver S}
    (f : ConeHom S X Y) (g : ConeHom S Y Z) :
    chosenAlgebraPullback S (f.hom ≫ g.hom) (ConeHom.compOverBase S f g) =
      chosenAlgebraPullback S g.hom g.overBase ≫
        chosenAlgebraPullback S f.hom f.overBase := sorry

end ConeOver


namespace ConeHom

/-- The composite of two cone morphisms is compatible with the explicit gradings. -/
theorem compCompatibleWithGrading {X Y Z : ConeOver S}
    (f : ConeHom S X Y) (g : ConeHom S Y Z) :
    coneHomCompatibleWithGrading S (f.hom ≫ g.hom) (compOverBase S f g) := sorry

/-- Composition of explicit cone morphisms. -/
def comp {X Y Z : ConeOver S} (f : ConeHom S X Y) (g : ConeHom S Y Z) :
    ConeHom S X Z where
  hom := f.hom ≫ g.hom
  overBase := compOverBase S f g
  compatibleWithGrading := compCompatibleWithGrading S f g

/-- Cone morphisms are equal when their underlying scheme morphisms are equal. -/
theorem ext {X Y : ConeOver S} {f g : ConeHom S X Y} (h : f.hom = g.hom) :
    f = g := sorry

/-- Left identity for explicit cone morphisms. -/
theorem id_comp {X Y : ConeOver S} (f : ConeHom S X Y) :
    comp S (id S X) f = f := sorry

/-- Right identity for explicit cone morphisms. -/
theorem comp_id {X Y : ConeOver S} (f : ConeHom S X Y) :
    comp S f (id S Y) = f := sorry

/-- Associativity of explicit cone-morphism composition. -/
theorem assoc {W X Y Z : ConeOver S}
    (f : ConeHom S W X) (g : ConeHom S X Y) (h : ConeHom S Y Z) :
    comp S (comp S f g) h = comp S f (comp S g h) := sorry

end ConeHom

/-- The category structure carried explicitly by cones over `S`. -/
@[reducible]
def coneCategory : Category (ConeOver S) where
  Hom X Y := ConeHom S X Y
  id := ConeHom.id S
  comp f g := ConeHom.comp S f g
  id_comp := ConeHom.id_comp S
  comp_id := ConeHom.comp_id S
  assoc := ConeHom.assoc S

/-- The bundled category of cones over `S`. -/
def coneCat : Cat :=
  ⟨ConeOver S, coneCategory S⟩

end AlgebraicGeometry.Scheme
