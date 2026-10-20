/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import ReasLib.CategoryTheory.Preadditive.Injective.Resolution.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition formulas for ordinary right derived functors

Right derived functors commute with postcomposition by a homology-preserving functor. They also
commute with precomposition by a homology-preserving functor that preserves injective objects.
The comparison isomorphisms are built from explicit injective resolutions; only their naturality
is deferred.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.NatIso

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable [HasInjectiveResolutions A]

/-- The right-derived transformations induced by the two directions of a functor isomorphism
compose to the identity. -/
theorem rightDerived_hom_inv_id
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (q : ℕ) :
    NatTrans.rightDerived e.hom q ≫ NatTrans.rightDerived e.inv q =
      𝟙 (F.rightDerived q) := sorry

/-- The reverse composite of the right-derived transformations induced by a functor
isomorphism is the identity. -/
theorem rightDerived_inv_hom_id
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (q : ℕ) :
    NatTrans.rightDerived e.inv q ≫ NatTrans.rightDerived e.hom q =
      𝟙 (G.rightDerived q) := sorry

/-- An isomorphism of additive functors induces an isomorphism of their right-derived functors
in every degree. -/
noncomputable def rightDerived
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (q : ℕ) :
    F.rightDerived q ≅ G.rightDerived q where
  hom := NatTrans.rightDerived e.hom q
  inv := NatTrans.rightDerived e.inv q
  hom_inv_id := rightDerived_hom_inv_id e q
  inv_hom_id := rightDerived_inv_hom_id e q

end CategoryTheory.NatIso

namespace CategoryTheory.Functor.RightDerived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C]

/-- The objectwise comparison between deriving a composite and applying a
homology-preserving functor after deriving. -/
noncomputable def postcompObjIso
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [G.PreservesHomology]
    [HasInjectiveResolutions A] (q : ℕ) (X : A) :
    ((F ⋙ G).rightDerived q).obj X ≅ (F.rightDerived q ⋙ G).obj X :=
  let I := injectiveResolution X
  I.isoRightDerivedObj (F ⋙ G) q ≪≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).mapIso
      ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℕ)).symm.app
        I.cocomplex) ≪≫
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).mapHomologyIso G q ≪≫
    G.mapIso (I.isoRightDerivedObj F q).symm

/-- The postcomposition comparison is natural in the source object. -/
@[reassoc]
theorem postcompObjIso_hom_naturality
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [G.PreservesHomology]
    [HasInjectiveResolutions A] (q : ℕ) {X Y : A} (f : X ⟶ Y) :
    ((F ⋙ G).rightDerived q).map f ≫ (postcompObjIso F G q Y).hom =
      (postcompObjIso F G q X).hom ≫ (F.rightDerived q ⋙ G).map f := sorry

/-- Right derivation commutes naturally with postcomposition by a homology-preserving functor. -/
noncomputable def postcompIso
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [G.PreservesHomology]
    [HasInjectiveResolutions A] (q : ℕ) :
    (F ⋙ G).rightDerived q ≅ F.rightDerived q ⋙ G :=
  NatIso.ofComponents (postcompObjIso F G q)
    (fun f ↦ postcompObjIso_hom_naturality F G q f)

/-- The objectwise comparison between deriving after a homology-preserving functor and
precomposing the derived functor. The first functor must preserve injective objects so that it
maps injective resolutions to injective resolutions. -/
noncomputable def precompObjIso
    (G : A ⥤ B) (F : B ⥤ C) [G.Additive] [F.Additive]
    [G.PreservesInjectiveObjects] [G.PreservesHomology]
    [HasInjectiveResolutions A] [HasInjectiveResolutions B] (q : ℕ) (X : A) :
    ((G ⋙ F).rightDerived q).obj X ≅ (G ⋙ F.rightDerived q).obj X :=
  let I := injectiveResolution X
  let GI := G.mapInjectiveResolution I
  I.isoRightDerivedObj (G ⋙ F) q ≪≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).mapIso
      ((mapHomologicalComplexCompIso (Iso.refl (G ⋙ F)) (ComplexShape.up ℕ)).symm.app
        I.cocomplex) ≪≫
    (GI.isoRightDerivedObj F q).symm

/-- The precomposition comparison is natural in the source object. -/
@[reassoc]
theorem precompObjIso_hom_naturality
    (G : A ⥤ B) (F : B ⥤ C) [G.Additive] [F.Additive]
    [G.PreservesInjectiveObjects] [G.PreservesHomology]
    [HasInjectiveResolutions A] [HasInjectiveResolutions B]
    (q : ℕ) {X Y : A} (f : X ⟶ Y) :
    ((G ⋙ F).rightDerived q).map f ≫ (precompObjIso G F q Y).hom =
      (precompObjIso G F q X).hom ≫ (G ⋙ F.rightDerived q).map f := sorry

/-- Right derivation commutes naturally with precomposition by a homology-preserving functor
that preserves injective objects. -/
noncomputable def precompIso
    (G : A ⥤ B) (F : B ⥤ C) [G.Additive] [F.Additive]
    [G.PreservesInjectiveObjects] [G.PreservesHomology]
    [HasInjectiveResolutions A] [HasInjectiveResolutions B] (q : ℕ) :
    (G ⋙ F).rightDerived q ≅ G ⋙ F.rightDerived q :=
  NatIso.ofComponents (precompObjIso G F q)
    (fun f ↦ precompObjIso_hom_naturality G F q f)

/-- Right derivation commutes with postcomposition by a bundled exact functor. -/
noncomputable abbrev postcompExactIso
    (F : A ⥤ B) (G : B ⥤ₑ C) [F.Additive] [HasInjectiveResolutions A] (q : ℕ) :
    (F ⋙ G.obj).rightDerived q ≅ F.rightDerived q ⋙ G.obj :=
  postcompIso F G.obj q

/-- Right derivation commutes with precomposition by a bundled exact functor that preserves
injective objects. -/
noncomputable abbrev precompExactIso
    (G : A ⥤ₑ B) (F : B ⥤ C) [G.obj.PreservesInjectiveObjects] [F.Additive]
    [HasInjectiveResolutions A] [HasInjectiveResolutions B] (q : ℕ) :
    (G.obj ⋙ F).rightDerived q ≅ G.obj ⋙ F.rightDerived q :=
  precompIso G.obj F q

/-- An isomorphism intertwining an additive functor with exact endofunctors induces the
corresponding isomorphism after right derivation.  Preservation of injectives is needed only for
the exact endofunctor acting on the source category. -/
@[stacks 01E8 "exact-square comparison for right derived functors"]
noncomputable def exactSquareIso
    (F : A ⥤ B) (T : B ⥤ₑ B) (S : A ⥤ₑ A) [F.Additive]
    [S.obj.PreservesInjectiveObjects] [HasInjectiveResolutions A]
    (e : F ⋙ T.obj ≅ S.obj ⋙ F) (q : ℕ) :
    F.rightDerived q ⋙ T.obj ≅ S.obj ⋙ F.rightDerived q :=
  (postcompExactIso F T q).symm ≪≫
    NatIso.rightDerived e q ≪≫
    precompExactIso S F q

end CategoryTheory.Functor.RightDerived
