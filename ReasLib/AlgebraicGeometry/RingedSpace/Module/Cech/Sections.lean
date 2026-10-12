/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.Algebra.Homology.Embedding.UpNat
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat.Homology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties
public import ReasLib.Topology.Opens.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-valued Cech and derived sections functors

This file owns the coefficient-functor layer shared by Cech delta functors and Cech-to-derived
comparisons. It contains no comparison choices: the Cech complex, its ordinary cohomology, its
bounded-derived realization, and bounded-derived sections are all canonical functor expressions.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable {ι : Type u} (cover : ι → Over U)

/-- The module-valued Cech complex of a family over an open subset, functorial in the module
sheaf. -/
@[stacks 01EQ "module Cech comparison source complex"]
abbrev complex :
    X.Modules ⥤ CochainComplex (ModuleCat (sectionsRingOnOpen X U)) ℕ :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    Presheaf.complex U cover

/-- The module-valued Cech complex is zero-morphism preserving after forgetting scalars. -/
instance complex_preservesZeroMorphisms :
    (complex U cover).PreservesZeroMorphisms := sorry

/-- The extended integer-indexed Cech row functor on module sheaves over a ringed space. -/
abbrev extended (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    X.Modules ⥤ CochainComplex (ModuleCat (RingedSpace.globalSectionsRing X)) ℤ :=
  complex (⊤ : Opens X.carrier)
      (fun i ↦ Over.mk (Opens.leTop (𝒰 i))) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat (RingedSpace.globalSectionsRing X))

/-- The extended Cech row functor preserves zero morphisms. -/
instance extended_preservesZeroMorphisms
    (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier) :
    (extended X 𝒰).PreservesZeroMorphisms := sorry

/-- Degree-`p` module-valued Cech cohomology, functorial in the module sheaf. -/
@[stacks 01EQ "module Cech cohomology functor"]
abbrev cohomologyFunctor (p : ℕ) :
    X.Modules ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  complex U cover ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat (sectionsRingOnOpen X U)) (ComplexShape.up ℕ) p

/-- The degree-`p` module-valued Cech cohomology of a presheaf module. -/
@[stacks 01EQ "presheaf module Cech cohomology"]
abbrev presheafCohomology (F : X.PresheafModules) (p : ℕ) :
    ModuleCat (sectionsRingOnOpen X U) :=
  Presheaf.cohomology U cover F p

/-- The degree-`p` module-valued Cech cohomology of a module sheaf. -/
@[stacks 01EQ "module Cech cohomology object"]
abbrev cohomology (F : X.Modules) (p : ℕ) :
    ModuleCat (sectionsRingOnOpen X U) :=
  (cohomologyFunctor U cover p).obj F

/-- The Cech complex, extended by zero and localized in the bounded-below derived category. -/
@[stacks 01EQ "derived module Cech source"]
abbrev derivedSource :
    X.Modules ⥤ DerivedCategory.Plus (ModuleCat (sectionsRingOnOpen X U)) :=
  complex U cover ⋙
    CochainComplex.Plus.extendNat (ModuleCat (sectionsRingOnOpen X U)) ⋙
    DerivedCategory.Plus.Q

/-- Bounded-below derived sections on `U`, restricted to module sheaves placed in degree zero. -/
@[stacks 01EQ "derived module cohomology target"]
abbrev derivedTarget :
    X.Modules ⥤ DerivedCategory.Plus (ModuleCat (sectionsRingOnOpen X U)) :=
  DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
    Functor.RightDerived.Bounded.functor (moduleSectionsEvaluationFunctor X U)

/-- The degree-`p` cohomology functor of canonical bounded-below derived sections on `U`. The
integer grading is shared directly with the derived category; Cech delta functors specialize it
to `(p : ℤ)` for `p : ℕ`. -/
@[stacks 01EQ "bounded-derived module cohomology"]
abbrev derivedCohomologyFunctor (p : ℤ) :
    X.Modules ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  Functor.RightDerived.Bounded.degree (moduleSectionsEvaluationFunctor X U) p



end AlgebraicGeometry.RingedSpace.ModuleCech
