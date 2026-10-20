/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Set.Defs
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberRank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison

/-!
# Rank loci of finite locally free modules on algebraic spaces

The fiber-rank level sets of a finite locally free `𝒪_X`-module on an algebraic
space are clopen subsets of `|X|`, realized as open-and-closed subspaces, and
are stable under pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The spectrum of a field is irreducible, so a field-valued point has a
generic point. -/
instance instIrreducibleSpace_fieldValuedPoint (p : FieldValuedPoint X) :
    IrreducibleSpace p.overObj.left := by
  change IrreducibleSpace (Spec (.of p.K))
  infer_instance

/-- The fiber rank of a finite locally free module at a point of `|X|`, computed
on a field-valued representative by restricting to the corresponding spectrum
of a field and taking the scheme-theoretic fiber rank at its generic point. -/
noncomputable def fiberFinrank (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    (x : Points X) : ℕ :=
  let p := Quotient.out x
  Scheme.Modules.fiberFinrank
    ((restrictToScheme p.overObj).obj ((pullback p.hom).obj E))
    (genericPoint p.overObj.left)

/-- The fiber rank is independent of the chosen field-valued representative. -/
theorem fiberFinrank_eq_schemeFiber (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (p : FieldValuedPoint X) :
    fiberFinrank E (Points.mk p) =
      Scheme.Modules.fiberFinrank
        ((restrictToScheme p.overObj).obj ((pullback p.hom).obj E))
        (genericPoint p.overObj.left) :=
  sorry

/-- Finite local freeness makes each fiber-rank level set clopen in `|X|`. -/
theorem fiberFinrank_isClopen (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    (r : ℕ) : IsClopen (setOf (fun x : Points X ↦ fiberFinrank E x = r)) :=
  sorry

/-- The clopen locus on which a finite locally free module has fiber rank `r`. -/
noncomputable def rankClopen (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    (r : ℕ) : Clopens (Points X) :=
  ⟨setOf (fun x : Points X ↦ fiberFinrank E x = r), fiberFinrank_isClopen E r⟩

/-- Membership in `rankClopen E r` means that the fiber rank is `r`. -/
theorem mem_rankClopen (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    (r : ℕ) (x : Points X) :
    x ∈ rankClopen E r ↔ fiberFinrank E x = r :=
  sorry

/-- The clopen rank loci of a finite locally free module cover `|X|`. -/
theorem rankClopen_iSup (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] :
    iSup (fun r : ℕ ↦ (rankClopen E r).toOpens) = ⊤ :=
  sorry

/-- Distinct clopen rank loci of a finite locally free module are disjoint. -/
theorem rankClopen_pairwiseDisjoint (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] :
    Pairwise fun r s : ℕ ↦
      Disjoint (rankClopen E r : Set (Points X)) (rankClopen E s : Set (Points X)) :=
  sorry

/-- Pullback of modules along a morphism of algebraic spaces preserves finite
local freeness. -/
instance pullback_isFiniteLocallyFree {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] :
    SheafOfModules.IsFiniteLocallyFree ((pullback g).obj E) :=
  sorry

/-- Rank loci commute with pullback of modules. -/
theorem rankClopen_pullback {Y : AlgebraicSpace S} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (g : Y ⟶ X) (r : ℕ) :
    (rankClopen ((pullback g).obj E) r : Set (Points Y)) =
      Points.map g ⁻¹' (rankClopen E r : Set (Points X)) :=
  sorry

/-- The open-and-closed subspace `X_r ⊂ X` on which `E` has rank `r`. -/
noncomputable def rankOpenSubspace (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (r : ℕ) : OpenSubspace X :=
  OpenSubspace.fromOpens (rankClopen E r).toOpens

/-- The underlying point-set of `rankOpenSubspace E r` is the clopen rank-`r`
locus. -/
theorem rankOpenSubspace_pointsSet (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (r : ℕ) :
    (rankOpenSubspace E r).pointsSet = rankClopen E r :=
  sorry

/-- The inclusion of a rank locus is an open immersion. -/
instance rankOpenSubspace_isOpenImmersion (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (r : ℕ) :
    IsOpenImmersion (rankOpenSubspace E r).ι :=
  (rankOpenSubspace E r).isOpenImmersion

/-- The inclusion of a rank locus is a closed immersion. -/
instance rankOpenSubspace_isClosedImmersion (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (r : ℕ) :
    IsClosedImmersion (rankOpenSubspace E r).ι :=
  sorry

/-- The inclusion of `rankOpenSubspace E r` is both an open and a closed
immersion. -/
theorem rankOpenSubspace_spec (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (r : ℕ) :
    IsOpenImmersion (rankOpenSubspace E r).ι ∧
      IsClosedImmersion (rankOpenSubspace E r).ι :=
  sorry

/-- Restriction of a finite locally free module to its rank-`r` locus has
constant rank `r`. -/
instance rankClopenPullback_isFiniteLocallyFreeOfRank (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((pullback (rankOpenSubspace E r).ι).obj E) :=
  sorry

/-- The restriction of `E` to its rank-`r` subspace. -/
noncomputable abbrev rankModule (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] (r : ℕ) :
    (rankOpenSubspace E r).X.Modules :=
  (pullback (rankOpenSubspace E r).ι).obj E

/-- `rankModule E r` is the pullback of `E` along the rank-`r` inclusion. -/
theorem rankModule_eq (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    (r : ℕ) :
    rankModule E r = (pullback (rankOpenSubspace E r).ι).obj E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
