/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0B8S

# The global-section action on sheaf cohomology

Global functions act on the cohomology of an `O_X`-module through their canonical central
endomorphisms of the module sheaf.  This gives the direct `Sheaf.H` model its reusable
`Gamma(X, O_X)`-module structure, without a local instance or a comparison chosen downstream.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Cohomology

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The action of a global function on sheaf cohomology, induced by its scalar endomorphism of
the coefficient module sheaf. -/
@[stacks 0EHA "global-section action on sheaf cohomology"]
noncomputable abbrev globalSMul (F : X.Modules) (p : ℕ)
    (r : globalSectionsRing X) (x : Sheaf.H ((moduleUnderlyingSheaf X).obj F) p) :
    Sheaf.H ((moduleUnderlyingSheaf X).obj F) p :=
  Sheaf.H.map ((moduleUnderlyingSheaf X).map (globalSectionMul r F)) p x

/-- The canonical scalar action of global functions on sheaf cohomology. -/
noncomputable instance globalSMulInst (F : X.Modules) (p : ℕ) :
    SMul (globalSectionsRing X) (Sheaf.H ((moduleUnderlyingSheaf X).obj F) p) where
  smul := globalSMul F p

/-- Global functions distribute over addition in sheaf cohomology. -/
theorem globalSMul_add (F : X.Modules) (p : ℕ) (r : globalSectionsRing X)
    (x y : Sheaf.H ((moduleUnderlyingSheaf X).obj F) p) :
    r • (x + y) = r • x + r • y := sorry

/-- Addition of global functions distributes over their action on sheaf cohomology. -/
theorem globalAdd_smul (F : X.Modules) (p : ℕ) (r s : globalSectionsRing X)
    (x : Sheaf.H ((moduleUnderlyingSheaf X).obj F) p) :
    (r + s) • x = r • x + s • x := sorry

/-- Multiplication of global functions agrees with iterated action on sheaf cohomology. -/
theorem globalMul_smul (F : X.Modules) (p : ℕ) (r s : globalSectionsRing X)
    (x : Sheaf.H ((moduleUnderlyingSheaf X).obj F) p) :
    (r * s) • x = r • s • x := sorry

/-- The unit global function acts identically on sheaf cohomology. -/
theorem globalOne_smul (F : X.Modules) (p : ℕ)
    (x : Sheaf.H ((moduleUnderlyingSheaf X).obj F) p) :
    (1 : globalSectionsRing X) • x = x := sorry

/-- Sheaf cohomology of an `O_X`-module is canonically a module over `Gamma(X, O_X)`. -/
@[stacks 0EHA "global-section module structure on sheaf cohomology",
  stacks 0B8S "global-section module structure on square-zero cohomology"]
noncomputable instance globalModule (F : X.Modules) (p : Nat) :
    Module (globalSectionsRing X) (Sheaf.H ((moduleUnderlyingSheaf X).obj F) p) :=
  Module.ofMinimalAxioms (globalSMul_add F p) (globalAdd_smul F p)
    (globalMul_smul F p) (globalOne_smul F p)

end AlgebraicGeometry.RingedSpace.Module.Cohomology
