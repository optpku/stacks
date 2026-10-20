module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Germ

/-! # Global functions and their étale germs -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsRestrict :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X),
    globalSectionsRing X ⟶ Γ((smallEtaleToScheme X).obj U, ⊤))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsToStructureSheaf :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X),
    (forget₂ CommRingCat RingCat).obj (globalSectionsRing X) ⟶
      (structureSheaf X).obj.obj (op U))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsConstPresheaf :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsToStructureSheafHom :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    globalSectionsConstPresheaf X ⟶ (structureSheaf X).obj)

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsToStructureSheafHom_app :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : (smallEtaleSite X)ᵒᵖ),
    (globalSectionsToStructureSheafHom X).app U =
      globalSectionsToStructureSheaf U.unop)

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsToEtaleLocalRing :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X),
    ((toSmallEtalePoint xbar).presheafFiber (A := RingCat.{u})).obj
        (globalSectionsConstPresheaf X) →+* etaleLocalRing X xbar)

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsToEtaleLocalRing_spec :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) (U : smallEtaleSite X)
    (l : (toSmallEtalePoint xbar).fiber.obj U) (a : globalSectionsRing X),
    globalSectionsToEtaleLocalRing X xbar
        (RingCat.Hom.hom
          ((toSmallEtalePoint xbar).toPresheafFiber U l
            (globalSectionsConstPresheaf X)) a) =
      RingCat.Hom.hom
        ((toSmallEtalePoint xbar).toPresheafFiber U l (structureSheaf X).obj)
        (globalSectionsToStructureSheaf U a))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsToFiberEtaleLocalRing :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) (zbar : GeometricPoint (fieldFiber f p)),
    ((toSmallEtalePoint (zbar.map (fieldFiberι f p))).presheafFiber (A := RingCat.{u})).obj
        (globalSectionsConstPresheaf X) →+* etaleLocalRing (fieldFiber f p) zbar)

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsToFiberEtaleLocalRingAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) (zbar : GeometricPoint (fieldFiber f p))
    (U : smallEtaleSite X)
    (l : (toSmallEtalePoint (zbar.map (fieldFiberι f p))).fiber.obj U),
    globalSectionsRing X →+* etaleLocalRing (fieldFiber f p) zbar)
