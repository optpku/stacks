/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

@[expose] public section

/-!
# Adjunctions on homotopy categories

This module transports an adjunction of additive functors to the homotopy categories of cochain
complexes. The Hom-set equivalence is defined directly on quotient representatives, which keeps
the computational part available to derived-functor constructions.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Adjunction

/-- The chain-complex adjunction induced by an adjunction of additive functors. -/
@[stacks 0DVC "adjunction on cochain complexes"]
noncomputable def mapHomologicalComplexAdjunction
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) (c : ComplexShape ℤ) :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c :=
  let unit :=
    (Functor.mapHomologicalComplexIdIso D c).inv ≫
      NatTrans.mapHomologicalComplex adj.unit c
  let counit :=
    NatTrans.mapHomologicalComplex adj.counit c ≫
      (Functor.mapHomologicalComplexIdIso C c).hom
  let triangleIdentities :
      (Functor.whiskerRight unit (G.mapHomologicalComplex c) ≫
          (Functor.associator (G.mapHomologicalComplex c)
            (F.mapHomologicalComplex c) (G.mapHomologicalComplex c)).hom ≫
          Functor.whiskerLeft (G.mapHomologicalComplex c) counit =
        NatTrans.id (𝟭 _ ⋙ G.mapHomologicalComplex c)) ∧
      (Functor.whiskerLeft (F.mapHomologicalComplex c) unit ≫
          (Functor.associator (F.mapHomologicalComplex c)
            (G.mapHomologicalComplex c) (F.mapHomologicalComplex c)).inv ≫
          Functor.whiskerRight counit (F.mapHomologicalComplex c) =
        NatTrans.id (F.mapHomologicalComplex c ⋙ 𝟭 _)) := by
    sorry
  Adjunction.mkOfUnitCounit {
    unit := unit
    counit := counit
    left_triangle := triangleIdentities.1
    right_triangle := triangleIdentities.2 }

/-- The Hom-set equivalence on homotopy categories induced by an adjunction of additive functors.
-/
@[stacks 0DVC "hom-set equivalence on cochain homotopy categories"]
noncomputable def mapHomotopyCategoryCoreHomEquiv
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) :
    Adjunction.CoreHomEquiv
      (G.mapHomotopyCategory (up ℤ))
      (F.mapHomotopyCategory (up ℤ)) := by
  let mappedG := G.mapHomotopyCategory (up ℤ)
  let mappedF := F.mapHomotopyCategory (up ℤ)
  let toFun (L : HomotopyCategory D (up ℤ)) (K : HomotopyCategory C (up ℤ))
      (f : mappedG.obj L ⟶ K) : L ⟶ mappedF.obj K :=
    (HomotopyCategory.quotient D (up ℤ)).map
      (((mapHomologicalComplexAdjunction adj (up ℤ)).homEquiv L.as K.as) f.out)
  let invFun (L : HomotopyCategory D (up ℤ)) (K : HomotopyCategory C (up ℤ))
      (g : L ⟶ mappedF.obj K) : mappedG.obj L ⟶ K :=
    (HomotopyCategory.quotient C (up ℤ)).map
      (((mapHomologicalComplexAdjunction adj (up ℤ)).homEquiv L.as K.as).symm g.out)
  let laws :
      (∀ L K f, invFun L K (toFun L K f) = f) ∧
      (∀ L K g, toFun L K (invFun L K g) = g) ∧
      (∀ {L' L K} (f : L' ⟶ L) (g : L ⟶ mappedF.obj K),
        invFun L' K (f ≫ g) = mappedG.map f ≫ invFun L K g) ∧
      (∀ {L K K'} (f : mappedG.obj L ⟶ K) (g : K ⟶ K'),
        toFun L K' (f ≫ g) = toFun L K f ≫ mappedF.map g) := by
    sorry
  let homEquiv (L : HomotopyCategory D (up ℤ)) (K : HomotopyCategory C (up ℤ)) :
      (mappedG.obj L ⟶ K) ≃ (L ⟶ mappedF.obj K) :=
    { toFun := toFun L K
      invFun := invFun L K
      left_inv := laws.1 L K
      right_inv := laws.2.1 L K }
  exact {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := laws.2.2.1
    homEquiv_naturality_right := laws.2.2.2 }

namespace mapHomotopyCategoryCoreHomEquiv

/-- The forward hom-set map is induced by the ambient cochain-level adjunction. -/
@[simp, stacks 0DVC "forward computation of the homotopy-category hom-equivalence"]
theorem apply
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F)
    {L : HomotopyCategory D (up ℤ)} {K : HomotopyCategory C (up ℤ)}
    (f : (G.mapHomotopyCategory (up ℤ)).obj L ⟶ K) :
    (mapHomotopyCategoryCoreHomEquiv adj).homEquiv L K f =
      (HomotopyCategory.quotient D (up ℤ)).map
        (((mapHomologicalComplexAdjunction adj (up ℤ)).homEquiv L.as K.as) f.out) := sorry

/-- The inverse hom-set map is induced by the inverse ambient cochain-level adjunction. -/
@[simp, stacks 0DVC "inverse computation of the homotopy-category hom-equivalence"]
theorem symm_apply
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F)
    {L : HomotopyCategory D (up ℤ)} {K : HomotopyCategory C (up ℤ)}
    (g : L ⟶ (F.mapHomotopyCategory (up ℤ)).obj K) :
    ((mapHomotopyCategoryCoreHomEquiv adj).homEquiv L K).symm g =
      (HomotopyCategory.quotient C (up ℤ)).map
        (((mapHomologicalComplexAdjunction adj (up ℤ)).homEquiv L.as K.as).symm g.out) := sorry

end mapHomotopyCategoryCoreHomEquiv

/-- An adjunction of additive functors induces an adjunction on homotopy categories of cochain
complexes. -/
noncomputable def mapHomotopyCategoryAdjunction
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) :
    G.mapHomotopyCategory (up ℤ) ⊣ F.mapHomotopyCategory (up ℤ) :=
  Adjunction.mkOfHomEquiv (mapHomotopyCategoryCoreHomEquiv adj)

/-- The bounded-below homotopy-category adjunction induced by an adjunction of additive functors.

The construction is the canonical restriction of `mapHomotopyCategoryAdjunction` to the
`HomotopyCategory.plus` full subcategories.  Preservation of bounded-below objects is supplied by
the standard `Functor.Homotopy.Plus.mapsTo` API, so callers do not rebuild local instances. -/
@[stacks 014X "bounded-below homotopy adjunction"]
noncomputable def mapHomotopyCategoryPlusAdjunction
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) :
    G.mapHomotopyCategoryPlus ⊣ F.mapHomotopyCategoryPlus :=
  ObjectProperty.FullSubcategory.adjunction
    (G.mapHomotopyCategory (up ℤ)) (F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategoryAdjunction adj)
    (Functor.Homotopy.Plus.mapsTo G) (Functor.Homotopy.Plus.mapsTo F)

end CategoryTheory.Adjunction
