module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood

/-! # Étale neighborhoods of geometric points and their morphisms -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

#check (etaleLiftFunctor : ∀ (xbar : GeometricPoint X),
    spacesEtaleSite X ⥤ Type (u + 1))

#check (etaleLiftFunctor_obj : ∀ (xbar : GeometricPoint X) (U : spacesEtaleSite X),
    (etaleLiftFunctor xbar).obj U =
      (Over.mk xbar.hom ⟶ (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj U))

#check (EtaleNeighborhood : (xbar : GeometricPoint X) → Type (u + 1))

#check (etaleNeighborhood_eq : ∀ (xbar : GeometricPoint X),
    EtaleNeighborhood xbar = (etaleLiftFunctor xbar).Elements)

namespace EtaleNeighborhood

variable {xbar : GeometricPoint X}

#check (toSpacesEtale : ∀ (U : EtaleNeighborhood xbar),
    spacesEtaleSite X)

#check (space : ∀ (U : EtaleNeighborhood xbar),
    AlgebraicSpace S)

#check (hom : ∀ (U : EtaleNeighborhood xbar),
    U.space ⟶ X)

#check (lift : ∀ (U : EtaleNeighborhood xbar),
    ofOver xbar.overObj ⟶ U.space)

#check (lift_fac : ∀ (U : EtaleNeighborhood xbar),
    U.lift ≫ U.hom = xbar.hom)

#check (geometricPoint : ∀ (U : EtaleNeighborhood xbar),
    GeometricPoint U.space)

#check (geometricPoint_hom : ∀ (U : EtaleNeighborhood xbar),
    (geometricPoint U).hom = U.lift)

#check (spec : ∀ (U : EtaleNeighborhood xbar),
    Etale U.hom ∧ U.lift ≫ U.hom = xbar.hom)

#check (of : ∀ (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom),
    EtaleNeighborhood xbar)

#check (of_toSpacesEtale : ∀ (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom),
    (of U u hu).toSpacesEtale = U)

#check (of_space : ∀ (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom),
    (of U u hu).space = U.left)

#check (of_hom : ∀ (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom),
    (of U u hu).hom = U.hom)

#check (of_lift : ∀ (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom),
    (of U u hu).lift = u)

#check (self : ∀ (xbar : GeometricPoint X),
    EtaleNeighborhood xbar)

#check (self_hom : ∀ (xbar : GeometricPoint X),
    (self xbar).hom = 𝟙 X)

#check (self_lift : ∀ (xbar : GeometricPoint X),
    (self xbar).lift = xbar.hom)

#check (Hom : (V U : EtaleNeighborhood xbar) → Type (u + 1))

namespace Hom

#check (toSpacesEtaleHom : ∀ {V U : EtaleNeighborhood xbar} (f : Hom V U),
    V.toSpacesEtale ⟶ U.toSpacesEtale)

#check (spaceHom : ∀ {V U : EtaleNeighborhood xbar} (f : Hom V U),
    V.space ⟶ U.space)

#check (lift_fac : ∀ {V U : EtaleNeighborhood xbar} (f : Hom V U),
    V.lift ≫ f.spaceHom = U.lift)

#check (over_fac : ∀ {V U : EtaleNeighborhood xbar} (f : Hom V U),
    f.spaceHom ≫ U.hom = V.hom)

#check (spec : ∀ {V U : EtaleNeighborhood xbar} (f : Hom V U),
    f.spaceHom ≫ U.hom = V.hom ∧ V.lift ≫ f.spaceHom = U.lift)

#check (of : ∀ {V U : EtaleNeighborhood xbar} (f : V.toSpacesEtale ⟶ U.toSpacesEtale)
    (hf : V.lift ≫ f.left = U.lift),
    Hom V U)

#check (of_toSpacesEtaleHom : ∀ {V U : EtaleNeighborhood xbar} (f : V.toSpacesEtale ⟶ U.toSpacesEtale)
    (hf : V.lift ≫ f.left = U.lift),
    (of f hf).toSpacesEtaleHom = f)

#check (of_spaceHom : ∀ {V U : EtaleNeighborhood xbar} (f : V.toSpacesEtale ⟶ U.toSpacesEtale)
    (hf : V.lift ≫ f.left = U.lift),
    (of f hf).spaceHom = f.left)

end Hom

end EtaleNeighborhood

end GeometricPoint

end AlgebraicGeometry.AlgebraicSpace
