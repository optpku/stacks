/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Compact

/-!
# Compact generation on pro-étale sites

The unbounded derived categories of abelian sheaves and module sheaves on the
small and big pro-étale sites of a scheme are compactly generated.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme.ProEt

/-- The unbounded derived category of abelian sheaves on the small pro-étale site
of a scheme is compactly generated. -/
theorem derivedAbelian_isCompactlyGenerated (S : Scheme.{u})
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [HasCoproducts (DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1}))] :
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})) := sorry

/-- The unbounded derived category of sheaves of modules over any ring on the
small pro-étale site of a scheme is compactly generated. -/
theorem derivedModule_isCompactlyGenerated
    (S : Scheme.{u}) (Λ : Type v) [Ring Λ]
    [HasWeakSheafify (topology S) (ModuleCat.{v} Λ)]
    [Abelian (Sheaf (topology S) (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf (topology S) (ModuleCat.{v} Λ))]
    [HasCoproducts (DerivedCategory (Sheaf (topology S) (ModuleCat.{v} Λ)))] :
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (topology S) (ModuleCat.{v} Λ))) := sorry

/-- The unbounded derived category of modules over any sheaf of rings on the
small pro-étale site of a scheme is compactly generated. -/
theorem derivedSheafOfModules_isCompactlyGenerated
    (S : Scheme.{u}) (A : Sheaf (topology S) RingCat.{w})
    [UnivLE.{u + 1, w}]
    [Abelian (SheafOfModules.{w} A)]
    [HasDerivedCategory (SheafOfModules.{w} A)]
    [HasCoproducts (DerivedCategory (SheafOfModules.{w} A))] :
    IsCompactlyGenerated (DerivedCategory (SheafOfModules.{w} A)) := sorry

/-- The unbounded derived category of abelian sheaves on the big pro-étale site
of a scheme is compactly generated. -/
theorem bigDerivedAbelian_isCompactlyGenerated (S : Scheme.{u})
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [HasCoproducts
      (DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}))] :
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})) := sorry

/-- The unbounded derived category of sheaves of modules over any ring on the
big pro-étale site of a scheme is compactly generated. -/
theorem bigDerivedModule_isCompactlyGenerated
    (S : Scheme.{u}) (Λ : Type v) [Ring Λ]
    [HasWeakSheafify (proetaleTopology.over S) (ModuleCat.{v} Λ)]
    [Abelian (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ))]
    [HasCoproducts
      (DerivedCategory (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ)))] :
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ))) := sorry

/-- The unbounded derived category of modules over any sheaf of rings on the
big pro-étale site of a scheme is compactly generated. -/
theorem bigDerivedSheafOfModules_isCompactlyGenerated
    (S : Scheme.{u}) (A : Sheaf (proetaleTopology.over S) RingCat.{w})
    [UnivLE.{u + 1, w}]
    [Abelian (SheafOfModules.{w} A)]
    [HasDerivedCategory (SheafOfModules.{w} A)]
    [HasCoproducts (DerivedCategory (SheafOfModules.{w} A))] :
    IsCompactlyGenerated (DerivedCategory (SheafOfModules.{w} A)) := sorry

end AlgebraicGeometry.Scheme.ProEt
