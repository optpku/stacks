/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckLarge
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-! The genus is the degree-one finrank of the canonical scheme-module
cohomology, with scalars induced by the structure morphism. This module
retains the challenge-facing signature without choosing a second resolution. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.CurveJacobian

theorem genusInjectiveResolutions (X : Scheme.{u}) :
    HasInjectiveResolutions X.Modules :=
  SheafOfModules.LargeSite.injectiveResolutions
    (Opens.grothendieckTopology X.carrier) X.ringCatSheaf

theorem genusEvaluationAdditive (X : Scheme.{u}) :
    (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : Opens X))).Additive := by
  exact { map_add := by intros; rfl }

/-- The genus of a smooth proper curve, computed as `dim_k H¹(C, O_C)`. -/
noncomputable def genus {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] : ℕ :=
  Scheme.Hom.cohomologyFinrank C.hom
    (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1

/-- The compatibility genus uses the canonical scheme-module cohomology and the scalar
action induced by the specified structure morphism. -/
theorem genus_eq_cohomologyFinrank {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    genus C = Scheme.Hom.cohomologyFinrank C.hom
      (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 := rfl

/-- A linear comparison with an actual computational model suffices to identify genus.
Constructing that comparison (for example from an acyclic Čech cover) remains a separate task. -/
theorem genus_eq_finrank_of_linearEquiv {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    {V : Type u} [AddCommGroup V] [Module k V]
    (e : Scheme.Hom.cohomology C.hom
      (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 ≃ₗ[k] V) :
    genus C = Module.finrank k V :=
  e.finrank_eq

end AlgebraicGeometry.CurveJacobian
