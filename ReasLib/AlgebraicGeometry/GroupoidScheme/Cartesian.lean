module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Category
public import ReasLib.AlgebraicGeometry.GroupoidScheme.PreRelation
import ReasLib.AlgebraicGeometry.GroupoidScheme.Inversion

/-!
# Cartesian morphisms of groupoid schemes

This module defines cartesian morphisms of groupoid schemes and the bundled category of
groupoid schemes cartesian over a fixed target.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

namespace Hom

/-- A morphism of groupoid schemes is cartesian when its underlying pre-relation morphism is
cartesian. -/
abbrev IsCartesian {S : Scheme.{u}} {G G' : GroupoidScheme S} (f : Hom G G') : Prop :=
  f.toPreRelation.IsCartesian

/-- Cartesianity is exactly the pullback condition on the arrow, source, and object maps. -/
theorem isCartesian_iff {S : Scheme.{u}} {G G' : GroupoidScheme S} (f : Hom G G') :
    f.IsCartesian ↔ IsPullback f.arrow.left G.s.left G'.s.left f.obj.left := by
  change f.toPreRelation.IsCartesian ↔
      IsPullback f.arrow.left G.s.left G'.s.left f.obj.left
  rw [Scheme.PreRelation.Hom.isCartesian_iff]
  rw [toPreRelation_arrow, toPreRelation_obj]
  rw [GroupoidScheme.toPreRelation_s, GroupoidScheme.toPreRelation_s]
  exact Iff.rfl

/-- A pullback target square of a groupoid-scheme morphism yields a pullback source square. -/
theorem sourceSquare_isPullback {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H)
    (hcart : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    IsPullback f.arrow.left G.s.left H.s.left f.obj.left := sorry

/-- A cartesian morphism of groupoid schemes also has a pullback target square. -/
theorem targetSquare_isPullback {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) (hf : f.IsCartesian) :
    IsPullback f.arrow.left G.t.left H.t.left f.obj.left := sorry

end Hom

/-- The bundled category of groupoid schemes equipped with a cartesian morphism to `G`. -/
abbrev CartesianOver {S : Scheme.{u}} (G : GroupoidScheme S) : Cat :=
  Cat.of (ObjectProperty.FullSubcategory
    (fun X : overCategory G ↦ Hom.IsCartesian X.hom))

namespace CartesianOver

/-- Construct a groupoid scheme cartesian over `G` from its structure morphism. -/
def ofHom {S : Scheme.{u}} {G G' : GroupoidScheme S} (f : Hom G' G)
    (hf : f.IsCartesian) : CartesianOver G :=
  ⟨Over.mk f, hf⟩

/-- The structure morphism of an object cartesian over `G` is cartesian. -/
theorem isCartesian {S : Scheme.{u}} {G : GroupoidScheme S} (X : CartesianOver G) :
    X.obj.hom.IsCartesian := sorry

/-- A morphism between groupoid schemes cartesian over `G` commutes with their structure
morphisms to `G`. -/
theorem hom_comm {S : Scheme.{u}} {G : GroupoidScheme S} {X Y : CartesianOver G}
    (f : X ⟶ Y) :
    Hom.comp f.hom.left Y.obj.hom = X.obj.hom := sorry

end CartesianOver

end AlgebraicGeometry.GroupoidScheme
