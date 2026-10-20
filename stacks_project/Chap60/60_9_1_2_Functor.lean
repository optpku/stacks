module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import Mathlib.CategoryTheory.Functor.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Crystalline

/-- The functor assigning an explicit trivial crystalline object to each small Zariski object.

The parameters `trivialObject` and `trivialMap` represent the source triple `(U, U, ∅)` and
its induced morphisms in the crystalline category. -/
def trivialFunctor
    (X S : Scheme.{u})
    (Cris : Scheme.{u} → Scheme.{u} → Type u)
    [Category (Cris X S)]
    (trivialObject : X.smallZariskiSite → Cris X S)
    (trivialMap : {U V : X.smallZariskiSite} → (U ⟶ V) →
      (trivialObject U ⟶ trivialObject V))
    (map_id : ∀ U : X.smallZariskiSite,
      trivialMap (𝟙 U) = 𝟙 (trivialObject U))
    (map_comp : ∀ {U V W : X.smallZariskiSite} (f : U ⟶ V) (g : V ⟶ W),
      trivialMap (f ≫ g) = trivialMap f ≫ trivialMap g) :
    X.smallZariskiSite ⥤ Cris X S where
  obj := trivialObject
  map := trivialMap
  map_id := map_id
  map_comp := map_comp

/-- The trivial crystalline functor acts on a Zariski morphism by `trivialMap`. -/
theorem trivialFunctor_map
    (X S : Scheme.{u})
    (Cris : Scheme.{u} → Scheme.{u} → Type u)
    [Category (Cris X S)]
    (trivialObject : X.smallZariskiSite → Cris X S)
    (trivialMap : {U V : X.smallZariskiSite} → (U ⟶ V) →
      (trivialObject U ⟶ trivialObject V))
    (map_id : ∀ U : X.smallZariskiSite,
      trivialMap (𝟙 U) = 𝟙 (trivialObject U))
    (map_comp : ∀ {U V W : X.smallZariskiSite} (f : U ⟶ V) (g : V ⟶ W),
      trivialMap (f ≫ g) = trivialMap f ≫ trivialMap g)
    {U V : X.smallZariskiSite} (f : U ⟶ V) :
    (trivialFunctor X S Cris trivialObject trivialMap map_id map_comp).map f =
      trivialMap f := sorry

end Crystalline
end Scheme
end AlgebraicGeometry
