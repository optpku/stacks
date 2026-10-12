/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Construction
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

#check (SheafOfModules.RingedSite.CotangentComplex.obj :
  ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}],
    (A : Sheaf J CommRingCat.{u}) → (B : Under A) →
      CochainComplex (SheafOfModules (SheafOfModules.RingedSite.ringSheaf J B.right)) ℤ)
