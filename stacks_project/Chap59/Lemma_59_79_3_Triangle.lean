/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.SupportTriangle
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.CategoryTheory.Functor.Derived.Model

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Abelian sheaves on the small étale site of a scheme. -/
abbrev EtaleSheaf (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- The homotopy category of integer-indexed cochain complexes of abelian étale sheaves. -/
abbrev EtaleHomotopy (X : Scheme.{u}) [Abelian (EtaleSheaf X)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] :=
  HomotopyCategory (EtaleSheaf X) (ComplexShape.up ℤ)

/-- The derived category of abelian étale sheaves. -/
abbrev EtaleDerived (X : Scheme.{u}) [Abelian (EtaleSheaf X)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasDerivedCategory (EtaleSheaf X)] := DerivedCategory (EtaleSheaf X)

/-- Quasi-isomorphisms in the homotopy category of abelian étale sheaves. -/
abbrev etaleQuasiIso (X : Scheme.{u}) [Abelian (EtaleSheaf X)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] :=
  HomotopyCategory.quasiIso (EtaleSheaf X) (ComplexShape.up ℤ)

/-- The localization from the étale homotopy category to the derived category. -/
abbrev etaleDerivedQuotient (X : Scheme.{u}) [Abelian (EtaleSheaf X)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasDerivedCategory (EtaleSheaf X)] : EtaleHomotopy X ⥤ EtaleDerived X :=
  DerivedCategory.Qh

/-- An explicit total right-derived model of an additive functor on abelian étale sheaves. -/
abbrev EtaleRightDerivedModel {X Y : Scheme.{u}}
    [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Y)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Y)]
    (F : EtaleSheaf X ⥤ EtaleSheaf Y) [F.Additive] :=
  RightDerived.Model
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ etaleDerivedQuotient Y)
    (etaleDerivedQuotient X) (etaleQuasiIso X)

/-- The canonical inclusion of the complementary open subscheme of a closed immersion. -/
abbrev etaleComplementInclusion {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionComplement i).toScheme ⟶ X :=
  (closedImmersionComplement i).ι

/-- Direct image on small-universe abelian étale sheaves. -/
noncomputable abbrev etaleDirectImage {X Z : Scheme.{u}} (i : Z ⟶ X) :
    EtaleSheaf Z ⥤ EtaleSheaf X :=
  Scheme.etaleAbelianPushforward i

/- Compatibility check for the shared étale support-triangle construction. -/
#check (Scheme.Etale.Support.triangle :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (_ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    Pretriangulated.Triangle (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})))

/- Compatibility check for the shared étale support-map construction. -/
#check (Scheme.Etale.Support.supportMap :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    Scheme.Etale.Support.derivedSupport i F ⟶
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)

end AlgebraicGeometry
