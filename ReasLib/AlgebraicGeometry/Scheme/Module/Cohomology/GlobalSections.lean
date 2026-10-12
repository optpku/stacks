/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Global-sections modules on scheme cohomology

This leaf gives the canonical module structure on cohomology over the global
section ring, and its restriction along a morphism to an affine scheme.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- Degree-`p` cohomology with scalars restricted along
`f : X ⟶ Spec R`, functorially in the scheme module. -/
noncomputable abbrev cohomologyFunctor
    (f : X ⟶ Spec (CommRingCat.of R)) (p : ℕ) : X.Modules ⥤ ModuleCat R :=
  Scheme.Modules.cohomologyFunctor X p ⋙
    ModuleCat.restrictScalars (globalSectionsMap f)

/-- The degree-`p` cohomology of a scheme module, viewed as an `R`-module by
restriction of scalars along a morphism `f : X ⟶ Spec R`. -/
noncomputable abbrev cohomology
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) : ModuleCat R :=
  (cohomologyFunctor f p).obj F

/-- Forgetting the affine-base scalar action agrees with forgetting the canonical
`Γ(X, ⊤)`-module structure. -/
@[simp]
theorem cohomology_forget
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat.{u}).obj (cohomology f F p) =
      (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology F p) := sorry

/-- Forgetting the affine-base scalar action on `cohomology f F p` recovers
the ordinary cohomology object of the underlying additive sheaf. -/
theorem cohomologyForget_obj_eq
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat.{u}).obj (cohomology f F p) =
      RingedSpace.moduleCohomology F p := sorry

/-- The dimension of scheme-module cohomology for the canonical scalar action induced by an
affine-base morphism.  This packages the morphism-dependent module datum so numerical clients do
not need to reconstruct a local instance. -/
noncomputable def cohomologyFinrank
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) : ℕ :=
  Module.finrank R (cohomology f F p)

/-- `cohomologyFinrank` is the ordinary module finrank for the scalar action induced by the
specified affine-base morphism. -/
theorem cohomologyFinrank_def
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) :
    cohomologyFinrank f F p =
      Module.finrank R (cohomology f F p) := sorry

end AlgebraicGeometry.Scheme.Hom
