/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Frobenius colimits of vector bundles

This module defines the sequential colimit of finite locally free modules under
absolute-Frobenius pullback and its relation to modules over the Frobenius-colimit sheaf.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FrobeniusColimit

/-- A small model of the bundled category of finite locally free `𝒪_S`-modules. -/
def vectorBundles (S : Scheme.{u}) : Cat.{u + 1, u + 1} :=
  Cat.of (AsSmall.{u + 1, u, u + 1} (ObjectProperty.FullSubcategory
    (fun E : S.Modules ↦ Scheme.Modules.IsFiniteLocallyFree E)))

/-- An object of `vectorBundles S` is finite locally free. -/
theorem vectorBundles_property (S : Scheme.{u}) (E : vectorBundles S) :
    Scheme.Modules.IsFiniteLocallyFree (ULift.down E).obj := sorry

/-- Absolute-Frobenius pullback preserves finite locally free module sheaves. -/
theorem pullback_mapsTo (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    (fun E : S.Modules ↦ Scheme.Modules.IsFiniteLocallyFree E) ≤
      ObjectProperty.inverseImage
        (fun E : S.Modules ↦ Scheme.Modules.IsFiniteLocallyFree E)
        (Scheme.Modules.pullback (Scheme.absoluteFrobenius p S)) := sorry

/-- Pullback by absolute Frobenius, restricted to finite locally free modules. -/
def pullback (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    vectorBundles S ⥤ vectorBundles S :=
  AsSmall.down ⋙
    ObjectProperty.FullSubcategory.restrict
      (Scheme.Modules.pullback (Scheme.absoluteFrobenius p S)) (pullback_mapsTo p S) ⋙
    AsSmall.up

/-- The underlying module of restricted Frobenius pullback is ordinary pullback. -/
theorem pullback_obj (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (E : vectorBundles S) :
    (ULift.down ((pullback p S).obj E)).obj =
      (Scheme.Modules.pullback (Scheme.absoluteFrobenius p S)).obj (ULift.down E).obj := sorry

/-- The sequential diagram of vector bundles under absolute-Frobenius pullback. -/
def vectorBundleDiagram (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    ℕ ⥤ Cat.{u + 1, u + 1} :=
  Functor.ofSequence (fun _ : ℕ ↦ (pullback p S).toCatHom)

/-- Every object of the vector-bundle Frobenius diagram is `vectorBundles S`. -/
theorem vectorBundleDiagram_obj (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.IsCharP p] (n : ℕ) :
    (vectorBundleDiagram p S).obj n = vectorBundles S := sorry

/-- Every successor map in the vector-bundle diagram is Frobenius pullback. -/
theorem vectorBundleDiagram_map_succ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.IsCharP p] (n : ℕ) :
    (vectorBundleDiagram p S).map (homOfLE n.le_succ) = (pullback p S).toCatHom := sorry

/-- The categorical sequential colimit of vector bundles under Frobenius pullback. -/
noncomputable def vectorBundleColimit (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.IsCharP p] : Cat.{u + 1, u + 1} :=
  colimit (vectorBundleDiagram p S)

/-- The functor from the `n`-th vector-bundle stage into its Frobenius colimit. -/
noncomputable def stage (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (n : ℕ) : vectorBundles S ⥤ vectorBundleColimit p S :=
  (colimit.ι (vectorBundleDiagram p S) n).toFunctor

/-- Successive stage functors identify a bundle with its Frobenius pullback. -/
theorem stage_succ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    (n : ℕ) :
    pullback p S ⋙ stage p S (n + 1) = stage p S n := sorry

/-- A small model of finite locally free modules over the Frobenius-colimit sheaf. -/
def finiteLocallyFreeModules (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] :
    Cat.{u + 1, u + 1} :=
  Cat.of (AsSmall.{u + 1, u, u + 1} (ObjectProperty.FullSubcategory
    (fun E : SheafOfModules.{u} (ringSheaf p S) ↦
      SheafOfModules.IsFiniteLocallyFree E)))

/-- An object over the Frobenius-colimit sheaf is finite locally free. -/
theorem finiteLocallyFreeModules_property (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.IsCharP p] (E : finiteLocallyFreeModules p S) :
    (fun M : SheafOfModules.{u} (ringSheaf p S) ↦
      SheafOfModules.IsFiniteLocallyFree M) (ULift.down E).obj := sorry

/-- For a quasi-compact and quasi-separated scheme of prime characteristic `p`, the
Frobenius colimit of finite locally free modules is equivalent to the category of finite
locally free modules over the Frobenius-colimit structure sheaf. -/
theorem vectorBundlesEquiv (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    Nonempty (vectorBundleColimit p S ≌ finiteLocallyFreeModules p S) := sorry

end AlgebraicGeometry.Scheme.FrobeniusColimit
