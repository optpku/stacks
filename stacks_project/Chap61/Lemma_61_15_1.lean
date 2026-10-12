/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Compact
public import stacks_project.Chap61.Definition_61_29_1_Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.15.1

The unbounded derived categories of abelian sheaves, `Λ`-modules, and modules
over a sheaf of rings, on both the small and the big pro-étale sites of a
scheme, are compactly generated.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.ProEt

/-- Lemma 61.15.1 (1): `D(S_proétale)` is compactly generated. -/
@[stacks 0F4Q]
theorem derivedAbelian_isCompactlyGenerated (S : Scheme.{u})
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [HasCoproducts (DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1}))] :
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})) := sorry

/-- Lemma 61.15.1 (2): `D(S_proétale, Λ)` is compactly generated. -/
@[stacks 0F4Q]
theorem derivedModule_isCompactlyGenerated
    (S : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (topology S) (ModuleCat.{v} Λ)]
    [Abelian (ProetaleModuleSheaf S Λ)]
    [HasDerivedCategory (ProetaleModuleSheaf S Λ)]
    [HasCoproducts (ProetaleDerived S Λ)] :
    IsCompactlyGenerated (ProetaleDerived S Λ) := sorry

/-- Lemma 61.15.1 (3): `D(S_proétale, A)` is compactly generated for any sheaf of
rings `A` on `S_proétale`. -/
@[stacks 0F4Q]
theorem derivedSheafOfModules_isCompactlyGenerated
    (S : Scheme.{u}) (A : Sheaf (topology S) CommRingCat.{w})
    [(topology S).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [UnivLE.{u + 1, w}]
    [HasCoproducts (RingedSiteDerived (topology S) A)] :
    IsCompactlyGenerated (RingedSiteDerived (topology S) A) := sorry

/-- Lemma 61.15.1 (4): `D((Sch/S)_proétale)` is compactly generated. -/
@[stacks 0F4Q]
theorem bigDerivedAbelian_isCompactlyGenerated (S : Scheme.{u})
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [HasCoproducts
      (DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}))] :
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})) := sorry

/-- Lemma 61.15.1 (5): `D((Sch/S)_proétale, Λ)` is compactly generated. -/
@[stacks 0F4Q]
theorem bigDerivedModule_isCompactlyGenerated
    (S : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (proetaleTopology.over S) (ModuleCat.{v} Λ)]
    [Abelian (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ))]
    [HasCoproducts
      (DerivedCategory (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ)))] :
    IsCompactlyGenerated
      (DerivedCategory (Sheaf (proetaleTopology.over S) (ModuleCat.{v} Λ))) := sorry

/-- Lemma 61.15.1 (6): `D((Sch/S)_proétale, A)` is compactly generated for any
sheaf of rings `A` on `(Sch/S)_proétale`. -/
@[stacks 0F4Q]
theorem bigDerivedSheafOfModules_isCompactlyGenerated
    (S : Scheme.{u}) (A : Sheaf (proetaleTopology.over S) CommRingCat.{w})
    [(proetaleTopology.over S).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [UnivLE.{u + 1, w}]
    [HasCoproducts (RingedSiteDerived (proetaleTopology.over S) A)] :
    IsCompactlyGenerated (RingedSiteDerived (proetaleTopology.over S) A) := sorry

end AlgebraicGeometry.Scheme.ProEt
