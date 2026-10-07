module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Hom
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf

/-!
# Functoriality of quotient sheaves of scheme pre-relations

This module constructs the maps on quotient presheaves and quotient sheaves induced by a
morphism of scheme pre-relations.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation.Hom

/-- The natural transformation on quotient presheaves induced by a morphism of
pre-relations. -/
def quotientPresheafMap {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U}
    {Q : PreRelation U'} (f : Hom P Q) : P.quotientPresheaf ⟶ Q.quotientPresheaf where
  app T := TypeCat.ofHom <| Quot.map (fun x : T.unop ⟶ U ↦ x ≫ f.obj)
    (fun _ _ h ↦ f.mapPointRel h)
  naturality := sorry

/-- The map on quotient presheaves sends the class of a point to the class of its composite
with the object map. -/
theorem quotientPresheafMap_mk {S : Scheme.{u}} {U U' T : Over S}
    {P : PreRelation U} {Q : PreRelation U'} (f : Hom P Q) (x : T ⟶ U) :
    f.quotientPresheafMap.app (op T) (Quot.mk (P.pointRel T) x) =
      Quot.mk (Q.pointRel T) (x ≫ f.obj) := sorry

/-- The morphism of quotient sheaves induced by a morphism of pre-relations. -/
noncomputable def quotientSheafMap {S : Scheme.{u}} {U U' : Over S}
    {P : PreRelation U} {Q : PreRelation U'} (f : Hom P Q)
    (J : GrothendieckTopology (Over S)) : P.quotientSheaf J ⟶ Q.quotientSheaf J :=
  (presheafToSheaf J (Type (u + 1))).map
    (Functor.whiskerRight f.quotientPresheafMap uliftFunctor.{u + 1, u})

/-- The quotient maps form a commutative square with the maps induced by a morphism of
pre-relations. -/
theorem quotientMap_naturality {S : Scheme.{u}} {U U' : Over S}
    {P : PreRelation U} {Q : PreRelation U'} (f : Hom P Q)
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] :
    P.quotientMap J ≫ f.quotientSheafMap J =
      J.uliftYoneda.{u + 1}.map f.obj ≫ Q.quotientMap J := sorry

end AlgebraicGeometry.Scheme.PreRelation.Hom
