module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.OverField

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.Hom.globalSectionsMap_equalizes :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (of k))))),
    ((Scheme.ΓSpecIso (of k)).inv ≫ (chosenPresentation X).U.hom.appTop) ≫
        (chosenPresentation X).tAppTop =
      ((Scheme.ΓSpecIso (of k)).inv ≫ (chosenPresentation X).U.hom.appTop) ≫
        (chosenPresentation X).sAppTop)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.globalSectionsMap_comp_ι :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (of k))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (of k))))),
    (globalSectionsRing_ι X).hom.comp (Hom.globalSectionsMap f) =
      Scheme.Hom.globalSectionsMap (chosenPresentation X).U.hom)

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsMap :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    k →+* globalSectionsRing X)

#check (AlgebraicGeometry.AlgebraicSpace.instAlgebra_globalSectionsRing :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    Algebra k (globalSectionsRing X))

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsAlg :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    CommAlgCat k)

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsAlgMap :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    k →+* globalSectionsAlg X)

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsSpecMap :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    Spec (globalSectionsRing X) ⟶ Spec (of k))

#check (AlgebraicGeometry.AlgebraicSpace.coe_globalSectionsAlg :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    (globalSectionsAlg X : Type u) = globalSectionsRing X)

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsAlgMap_eq :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    globalSectionsAlgMap X = globalSectionsMap X)

#check (AlgebraicGeometry.AlgebraicSpace.globalSectionsSpecMap_eq :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    globalSectionsSpecMap X = Spec.map (ofHom (algebraMap k (globalSectionsRing X))))

end AlgebraicGeometry.AlgebraicSpace
