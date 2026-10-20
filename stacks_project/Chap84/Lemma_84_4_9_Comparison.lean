module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Cohomology.Restriction

/-! Compatibility interface for abelian étale cohomology and restriction. -/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `etaleCohomologyRestrict`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

#check (AlgebraicGeometry.AlgebraicSpace.etaleCohomology :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ),
    AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.etaleCohomology_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ),
    etaleCohomology X F q = ((globalSections X).rightDerived q).obj F)

#check (AlgebraicGeometry.AlgebraicSpace.homConstantPushforwardIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}),
    (globalSections X).obj ((sheafPushforwardAbelian f).obj G) ≅
      (globalSections Y).obj G)

#check (AlgebraicGeometry.AlgebraicSpace.homConstantPushforwardIso_hom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
    (φ : (globalSections X).obj ((sheafPushforwardAbelian f).obj G)),
    (homConstantPushforwardIso f G).hom φ =
      inv (CharacterSections.inverseImageConstantHom f) ≫
        ((sheafInverseImageAdjunction f).homEquiv (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1}
              (smallEtaleTopology X)) G).symm φ)

#check (AlgebraicGeometry.AlgebraicSpace.etaleAbelianSectionsRestrict :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})],
    globalSections X ⟶
      sheafInverseImage AddCommGrpCat.{u + 1} f ⋙ globalSections Y)

#check (AlgebraicGeometry.AlgebraicSpace.etaleAbelianSectionsRestrict_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    (etaleAbelianSectionsRestrict f).app F =
      (globalSections X).map ((sheafInverseImageAdjunction f).unit.app F) ≫
        (homConstantPushforwardIso f
          ((sheafInverseImage AddCommGrpCat.{u + 1} f).obj F)).hom)

#check (AlgebraicGeometry.AlgebraicSpace.etaleCohomologyRestrict :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ),
    etaleCohomology X F q ⟶
      etaleCohomology Y ((sheafInverseImage AddCommGrpCat.{u + 1} f).obj F) q)

#check (AlgebraicGeometry.AlgebraicSpace.etaleCohomologyRestrict_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ),
    etaleCohomologyRestrict f F q =
      Functor.RightDerived.exactSquareApp (globalSections X) (globalSections Y)
        (sheafInverseImage AddCommGrpCat.{u + 1} f) (𝟭 AddCommGrpCat.{u + 1})
        (etaleAbelianSectionsRestrict f) q F)
