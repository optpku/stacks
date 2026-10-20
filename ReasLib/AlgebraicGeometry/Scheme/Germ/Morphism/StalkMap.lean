module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Category

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Germ

namespace Hom.Representative

/-- The local-ring map induced by a representative of a morphism of scheme germs. -/
def stalkMap {X Y : Germ} (r : Representative X Y) :
    Y.scheme.presheaf.stalk Y.point ⟶ X.scheme.presheaf.stalk X.point :=
  (r.map_point ▸ r.hom.stalkMap (X.pointIn r.neighborhood r.mem_neighborhood)) ≫
    (r.neighborhood.stalkIso (X.pointIn r.neighborhood r.mem_neighborhood)).hom

/-- Equivalent representatives induce the same map on the distinguished stalks. -/
theorem stalkMap_respects {X Y : Germ} {r s : Representative X Y}
    (h : Equivalent r s) : stalkMap r = stalkMap s := sorry

end Hom.Representative

namespace Hom

/-- The canonical local-ring map induced contravariantly by a morphism of scheme germs. -/
def stalkMap {X Y : Germ} (f : X ⟶ Y) :
    Y.scheme.presheaf.stalk Y.point ⟶ X.scheme.presheaf.stalk X.point :=
  Representative.stalkMap (Quotient.out f)

/-- The stalk map of a represented germ morphism is the representative-level stalk map. -/
theorem stalkMap_mk {X Y : Germ} (r : Representative X Y) :
    stalkMap (mk r) = r.stalkMap := sorry

/-- The identity germ morphism induces the identity on the distinguished stalk. -/
theorem stalkMap_id (X : Germ) :
    stalkMap (𝟙 X) = 𝟙 (X.scheme.presheaf.stalk X.point) := sorry

/-- Stalk maps turn composition of germ morphisms into contravariant composition. -/
theorem stalkMap_comp {X Y Z : Germ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    stalkMap (f ≫ g) = stalkMap g ≫ stalkMap f := sorry

/-- The stalk map induced by a morphism of scheme germs is a local ring homomorphism. -/
instance instIsLocalHomStalkMap {X Y : Germ} (f : X ⟶ Y) :
    IsLocalHom f.stalkMap.hom := sorry

end Hom

namespace MorphismProperty

/-- Lift a property of commutative-ring homomorphisms to morphisms of scheme germs by testing
the induced map on the distinguished stalks. -/
def stalkwise
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) :
    CategoryTheory.MorphismProperty Germ.{u} :=
  fun _ _ f ↦ P f.stalkMap.hom

/-- The germ-morphism property `stalkwise P` is exactly `P` for the distinguished stalk map. -/
theorem stalkwise_iff
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    {X Y : Germ} (f : X ⟶ Y) : stalkwise P f ↔ P f.stalkMap.hom := sorry

end MorphismProperty

end AlgebraicGeometry.Scheme.Germ
