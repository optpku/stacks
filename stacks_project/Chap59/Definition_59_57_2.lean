/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Definition_59_57_2_TopRep
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants
public import ReasLib.FieldTheory.Galois.Cohomology
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory
open CategoryTheory.Action.ModuleCat

section TopologicalGroup

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- Definition 59.57.2 (1): continuous group cohomology is the right derived
functor of invariants on discrete continuous integer modules. -/
@[stacks 04JR] #check
  (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor ℤ G :
    ℕ → DiscreteModuleCat ℤ G ⥤ ModuleCat.{v} ℤ)

variable [DiscreteTopology G]

/- Definition 59.57.2 (2): for a group with the discrete topology, the same
right derived invariants functors are called group cohomology. -/
@[stacks 04JR] #check
  (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor ℤ G :
    ℕ → DiscreteModuleCat ℤ G ⥤ ModuleCat.{v} ℤ)

end TopologicalGroup

section GaloisExtension

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsGalois K L]

/- Definition 59.57.2 (3): for a Galois group with its Krull topology, the same
right derived invariants functors are called Galois cohomology. -/
@[stacks 04JR] #check
  (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor ℤ Gal(L/K) :
    ℕ → DiscreteModuleCat ℤ Gal(L/K) ⥤ ModuleCat.{v} ℤ)

end GaloisExtension

section AbsoluteGaloisGroup

variable (K : Type u) [Field K]

/- Definition 59.57.2 (4): field cohomology with coefficients in an absolute
Galois module is right derived invariants for the absolute Galois group. -/
@[stacks 04JR] #check (Field.galoisCohomology K :
  DiscreteModuleCat ℤ (Field.absoluteGaloisGroup K) → ℕ → ModuleCat.{u} ℤ)

end AbsoluteGaloisGroup
