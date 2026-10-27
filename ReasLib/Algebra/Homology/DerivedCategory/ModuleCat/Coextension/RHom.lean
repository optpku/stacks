/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open DerivedCategory.InternalHom

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedCoextension

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Restricting derived coextension of scalars identifies it with canonical derived internal Hom
over the source ring from the restricted regular module of the target ring. -/
@[stacks 0A71]
theorem restrictionIsomorphicRHom
    (f : A →+* B) (K : DerivedCategory (ModuleCat A)) :
    IsIsomorphic
      ((derivedRestrictionOfScalars f).obj ((derivedCoextensionOfScalars f).obj K))
      (RHom.obj
        (single0 ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) K) := sorry

/-- In each degree, homology of restricted derived coextension agrees with homology of canonical
derived internal Hom from the restricted regular module. -/
@[stacks 0A71]
theorem homologyRestrictionIsomorphicRHom
    (f : A →+* B) (K : DerivedCategory (ModuleCat A)) (q : ℤ) :
    IsIsomorphic
      ((ModuleCat.restrictScalars f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat B) q).obj
          ((derivedCoextensionOfScalars f).obj K)))
      ((DerivedCategory.homologyFunctor (ModuleCat A) q).obj
        (RHom.obj
          (single0 ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) K)) := sorry

end CategoryTheory.ModuleCat.DerivedCoextension
