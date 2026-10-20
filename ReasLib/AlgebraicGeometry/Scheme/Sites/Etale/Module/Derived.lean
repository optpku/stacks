/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Functors
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.Small
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open AlgebraicGeometry.StandardTopology.Big

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale.Module.Derived

variable {S T : Scheme.{u}}

/-- The unbounded derived small-site module direct image. -/
noncomputable def smallDirectImage (f : T ⟶ S) [UnivLE.{u + 1, v}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{v}]
    [T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{v}]
    [S.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [IsGrothendieckAbelian (SheafOfModules.{v} (Small.structureSheaf T))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf T))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf S))]
    [(Module.smallDirectImage f).Additive] :
    DerivedCategory (SheafOfModules.{v} (Small.structureSheaf T)) ⥤
      DerivedCategory (SheafOfModules.{v} (Small.structureSheaf S)) :=
  CategoryTheory.Adjunction.Derived.KInjective.right (Module.smallDirectImage f)

/-- The unbounded derived big-site module direct image. -/
noncomputable def bigDirectImage (f : T ⟶ S) [UnivLE.{u + 1, v}]
    [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(T.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{v}]
    [(S.overGrothendieckTopology @Etale).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [IsGrothendieckAbelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [(Module.bigDirectImage f).Additive] :
    DerivedCategory
        (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T)) ⥤
      DerivedCategory
        (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S)) :=
  CategoryTheory.Adjunction.Derived.KInjective.right (Module.bigDirectImage f)

/-- The exact module restriction from a big étale site to a small étale site. -/
noncomputable def relocalizationExact (f : T ⟶ S) [UnivLE.{u + 1, v}]
    :
    SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S) ⥤ₑ
      SheafOfModules.{v} (Small.structureSheaf T) :=
  ⟨Module.relocalization f, sorry⟩

/-- The derived module restriction from a big étale site to a small étale site. -/
noncomputable def relocalization (f : T ⟶ S) [UnivLE.{u + 1, v}]
    [Abelian (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [Abelian (SheafOfModules.{v} (Small.structureSheaf T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [HasDerivedCategory (SheafOfModules.{v} (Small.structureSheaf T))] :
    DerivedCategory
        (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S)) ⥤
      DerivedCategory (SheafOfModules.{v} (Small.structureSheaf T)) :=
  (relocalizationExact f).mapDerivedCategory

/-- The exact big-site module inverse image along postcomposition. -/
noncomputable def bigInverseImageExact (f : T ⟶ S) [UnivLE.{u + 1, v}]
    :
    SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S) ⥤ₑ
      SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T) :=
  ⟨Module.bigInverseImage f, sorry⟩

/-- The derived big-site module inverse image along postcomposition. -/
noncomputable def bigInverseImage (f : T ⟶ S) [UnivLE.{u + 1, v}]
    [Abelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [Abelian
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S))]
    [HasDerivedCategory
      (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T))] :
    DerivedCategory
        (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S)) ⥤
      DerivedCategory
        (SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T)) :=
  (bigInverseImageExact f).mapDerivedCategory

end AlgebraicGeometry.Scheme.Etale.Module.Derived

end
