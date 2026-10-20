module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood

variable {S : Scheme.{u}} {s : S}

#check (CategoryTheory.categoryOfElements
  (Etale.forget S ⋙ FunctorToTypes.fromOverFunctor Scheme.forget s) :
    Category (EtaleNeighborhood S s))

#check (Hom :
  EtaleNeighborhood S s → EtaleNeighborhood S s → Type u)

#check (CategoryTheory.CategoryOfElements.ext
  (Etale.forget S ⋙ FunctorToTypes.fromOverFunctor Scheme.forget s) :
    ∀ {U V : EtaleNeighborhood S s} (f g : Hom U V),
      f.toEtaleHom = g.toEtaleHom → f = g)

#check (CategoryTheory.CategoryOfElements.id_val :
  ∀ {U : EtaleNeighborhood S s},
    Hom.toEtaleHom (𝟙 U : U ⟶ U) = 𝟙 U.toEtale)

#check (CategoryTheory.CategoryOfElements.comp_val :
  ∀ {U V W : EtaleNeighborhood S s} {f : Hom U V} {g : Hom V W},
    Hom.toEtaleHom (f ≫ g) = f.toEtaleHom ≫ g.toEtaleHom)

#check (Elementary :
  ∀ (S : Scheme.{u}) (s : S), Type (u + 1))

#check (Elementary.of :
  ∀ {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s),
    U.IsElementary → Elementary S s)

#check (Elementary.isElementary :
  ∀ {S : Scheme.{u}} {s : S} (U : Elementary S s), U.obj.IsElementary)

#check (Elementary.of_obj :
  ∀ {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) (hU : U.IsElementary),
    (Elementary.of U hU).obj = U)

end AlgebraicGeometry.Scheme.EtaleNeighborhood
