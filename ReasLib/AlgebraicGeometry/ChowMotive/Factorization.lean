/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Retract
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Monoidal
public import ReasLib.AlgebraicGeometry.Correspondence.Category.Linear
public import ReasLib.AlgebraicGeometry.Correspondence.Monoidal
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Linear
public import ReasLib.AlgebraicGeometry.Correspondence.ProjectiveLine.Object
public import ReasLib.AlgebraicGeometry.ChowMotive

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents
open scoped CategoryTheory.MonoidalCategory

noncomputable section

universe w v u

namespace ChowMotive

open AlgebraicGeometry AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The underlying functor placing degree-zero correspondences in Tate degree zero and
then in the Karoubi envelope. -/
def inclusionFunctor (k : Type u) [Field k] :
    Correspondence.Category k ⥤
      ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) where
  obj X := (toKaroubi (Correspondence.GradedCategory k)).obj (X, 0)
  map f := (toKaroubi (Correspondence.GradedCategory k)).map
    (Correspondence.GradedCategory.homOfDegreeZero rfl f)
  map_id := sorry
  map_comp := sorry

/-- The degree-zero underlying inclusion places an object in Tate degree zero. -/
theorem inclusionFunctor_obj (X : Correspondence.Category k) :
    (inclusionFunctor k).obj X =
      (toKaroubi (Correspondence.GradedCategory k)).obj (X, 0) := sorry

/-- The degree-zero underlying inclusion maps a correspondence by the canonical Karoubi
embedding. -/
theorem inclusionFunctor_map {X Y : Correspondence.Category k} (f : X ⟶ Y) :
    (inclusionFunctor k).map f =
      (toKaroubi (Correspondence.GradedCategory k)).map
        (@Correspondence.GradedCategory.homOfDegreeZero k _ (X, 0) (Y, 0) rfl f) := sorry

/-- The schemes underlying the tensor units used by the graded and degree-zero
correspondence categories are canonically identical. -/
def inclusionUnitSchemeIso (k : Type u) [Field k] :
    (𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).X.1.scheme ≅
      ((inclusionFunctor k).obj (𝟙_ (Correspondence.Category k))).X.1.scheme :=
  (SchemeOverField.pointIsTerminal k).uniqueUpToIso
    ((Correspondence.Category.scheme_unit k).symm ▸ SchemeOverField.pointIsTerminal k)

/-- The unit-scheme comparison is the unique morphism of terminals from the graded tensor
unit scheme to the image of the degree-zero unit. -/
theorem inclusionUnitSchemeIso_hom (k : Type u) [Field k] :
    (inclusionUnitSchemeIso k).hom =
      CategoryTheory.Limits.IsTerminal.from
        ((Correspondence.Category.scheme_unit k).symm ▸ SchemeOverField.pointIsTerminal k)
        (𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).X.1.scheme := sorry

/-- The strong symmetric monoidal inclusion of degree-zero Chow correspondences into
Chow motives, placing every object in Tate degree zero with identity projector. -/
def inclusion (k : Type u) [Field k] :
    LaxBraidedFunctor (Correspondence.Category k)
      (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) where
  toFunctor := inclusionFunctor k
  laxBraided :=
    { ε :=
        { f := Correspondence.GradedCategory.homOfDegreeZero rfl
            (Correspondence.rationalGraphIso
              (𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).X.1
              ((inclusionFunctor k).obj (𝟙_ (Correspondence.Category k))).X.1
              (inclusionUnitSchemeIso k))
          comm := sorry }
      μ := fun X Y ↦
        { f := Correspondence.GradedCategory.homOfDegreeZero rfl
            (Correspondence.rationalGraphIso
              (((inclusionFunctor k).obj X ⊗ (inclusionFunctor k).obj Y).X.1)
              ((inclusionFunctor k).obj (X ⊗ Y)).X.1 (Iso.refl _))
          comm := sorry }
      μ_natural_left := sorry
      μ_natural_right := sorry
      associativity := sorry
      left_unitality := sorry
      right_unitality := sorry
      braided := sorry }

/-- On objects, `inclusion k` places a correspondence object in Tate degree zero with
identity projector. -/
theorem inclusion_obj (X : Correspondence.Category k) :
    (inclusion k).obj X =
      (toKaroubi (Correspondence.GradedCategory k)).obj (X, 0) := sorry

/-- On morphisms, the underlying graded map of `inclusion k` is the degree-zero
correspondence supplied to it. -/
theorem inclusion_map {X Y : Correspondence.Category k} (f : X ⟶ Y) :
    ((inclusion k).map f).f =
      @Correspondence.GradedCategory.homOfDegreeZero k _ (X, 0) (Y, 0) rfl f := sorry

/-- The degree-zero inclusion is `ℚ`-linear. -/
instance inclusionLinear : (inclusion k).toFunctor.Linear ℚ where
  map_smul := sorry

/-- The unit comparison of the degree-zero inclusion is an isomorphism. -/
instance inclusionUnitIsIso : IsIso (Functor.LaxMonoidal.ε (inclusion k).toFunctor) := sorry

/-- Every tensor comparison of the degree-zero inclusion is an isomorphism. -/
instance inclusionTensoratorIsIso (X Y : Correspondence.Category k) :
    IsIso (Functor.LaxMonoidal.μ (inclusion k).toFunctor X Y) := sorry

/-- Restrict a lax braided functor on Chow motives to degree-zero correspondences. -/
def restriction (k : Type u) [Field k] (C : Type v) [Category.{w} C]
    [MonoidalCategory C] [SymmetricCategory C] :
    LaxBraidedFunctor (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) C ⥤
      LaxBraidedFunctor (Correspondence.Category k) C where
  obj G := LaxBraidedFunctor.of ((inclusion k).toFunctor ⋙ G.toFunctor)
  map α := ⟨⟨Functor.whiskerLeft (inclusion k).toFunctor α.hom.hom, sorry⟩⟩
  map_id := sorry
  map_comp := sorry

/-- Restriction is precomposition with the degree-zero inclusion on underlying functors. -/
theorem restriction_obj (C : Type v) [Category.{w} C] [MonoidalCategory C]
    [SymmetricCategory C]
    (G : LaxBraidedFunctor (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) C) :
    ((restriction k C).obj G).toFunctor = (inclusion k).toFunctor ⋙ G.toFunctor := sorry

/-- Restriction acts on monoidal natural transformations by left whiskering with the
degree-zero inclusion. -/
theorem restriction_map (C : Type v) [Category.{w} C] [MonoidalCategory C]
    [SymmetricCategory C]
    {G H : LaxBraidedFunctor (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) C}
    (α : G ⟶ H) :
    ((restriction k C).map α).hom.hom =
      Functor.whiskerLeft (inclusion k).toFunctor α.hom.hom := sorry

/-- A strong symmetric monoidal, `ℚ`-linear extension of a functor from degree-zero
correspondences to Chow motives, together with its comparison after restriction. -/
structure Factorization (k : Type u) [Field k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear ℚ C] [MonoidalCategory C] [SymmetricCategory C]
    (F : Correspondence.Category k ⥤ C) [F.Braided] where
  /-- The extension to Chow motives. -/
  lift : LaxBraidedFunctor (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) C
  /-- The lax unit map of the extension is invertible. -/
  unitIsIso : IsIso (Functor.LaxMonoidal.ε lift.toFunctor)
  /-- The lax tensor maps of the extension are invertible. -/
  tensoratorIsIso : ∀ X Y, IsIso (Functor.LaxMonoidal.μ lift.toFunctor X Y)
  /-- The extension is `ℚ`-linear. -/
  linear : lift.toFunctor.Linear ℚ
  /-- Restricting the extension recovers the original functor monoidally. -/
  comparison : (restriction k C).obj lift ≅ LaxBraidedFunctor.of F

namespace Factorization

variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear ℚ C]
  [MonoidalCategory C] [SymmetricCategory C]
  {F : Correspondence.Category k ⥤ C} [F.Braided]

/-- Package a braided, strong monoidal, `ℚ`-linear extension and its comparison as a
factorization. -/
def of (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤ C)
    [G.Braided] [G.Linear ℚ]
    (comparison : (restriction k C).obj (LaxBraidedFunctor.of G) ≅
      LaxBraidedFunctor.of F) : Factorization k F where
  lift := LaxBraidedFunctor.of G
  unitIsIso := sorry
  tensoratorIsIso := fun _ _ ↦ sorry
  linear := { map_smul := Functor.Linear.map_smul (F := G) }
  comparison := comparison

/-- The lax structure stored by a factorization canonically determines its strong monoidal
structure. -/
@[implicit_reducible]
def monoidal (P : Factorization k F) : P.lift.toFunctor.Monoidal :=
  @Functor.Monoidal.ofLaxMonoidal _ _ _ _ _ _ P.lift.toFunctor
    P.lift.laxBraided.toLaxMonoidal P.unitIsIso P.tensoratorIsIso

/-- The monoidal structure recovered from a factorization has the stored lax-monoidal
structure. -/
theorem monoidal_toLaxMonoidal (P : Factorization k F) :
    (monoidal P).toLaxMonoidal = P.lift.laxBraided.toLaxMonoidal := sorry

end Factorization

end ChowMotive

namespace ChowMotive.ProjectiveLine

open AlgebraicGeometry AlgebraicGeometry.Correspondence CategoryTheory
open CategoryTheory.Idempotents
open scoped CategoryTheory.MonoidalCategory

/-- A `ℚ`-linear strong symmetric monoidal functor on degree-zero Chow correspondences
whose image of `timesPoint x` splits as a tensor-invertible retract of the image of
`ℙ¹` extends uniquely, up to a unique compatible monoidal isomorphism, to Chow motives. -/
theorem existsUniqueFactorization {k : Type u} [Field k]
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear ℚ C]
    [MonoidalCategory C] [SymmetricCategory C] [IsIdempotentComplete C]
    (F : Correspondence.Category k ⥤ C) [F.Braided] [F.Linear ℚ]
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1)
    (U : C) [MonoidalCategory.isInvertibleObject U]
    (r : Retract U (F.obj (Correspondence.ProjectiveLine.asObject k)))
    (h_c2 : let c₂ : Correspondence.ProjectiveLine.asObject k ⟶
        Correspondence.ProjectiveLine.asObject k :=
      Correspondence.ProjectiveLine.timesPoint x
      r.r ≫ r.i = F.map c₂) :
    ∃ P : ChowMotive.Factorization k F, ∀ Q : ChowMotive.Factorization k F,
      ∃! e : P.lift ≅ Q.lift,
        (ChowMotive.restriction k C).mapIso e ≪≫ Q.comparison = P.comparison := sorry

end ChowMotive.ProjectiveLine
