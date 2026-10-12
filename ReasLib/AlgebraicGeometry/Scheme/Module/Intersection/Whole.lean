/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Degree

/-!
# Whole-scheme intersection degree

This leaf records the canonical bottom-ideal closed subscheme and the
specialization of intersection degree to it.  Both the ambient scheme and the
closed subscheme use the canonical scheme-module tensor product.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- The bottom-ideal closed subscheme has the same topological Krull dimension as the ambient
scheme. -/
theorem topologicalKrullDim_bot_eq
    (X : Scheme.{u}) {d : ℕ} (hXdim : topologicalKrullDim X = d) :
    topologicalKrullDim ((⊥ : X.IdealSheafData).subscheme) = d := sorry

/-- The intersection degree of the whole scheme, represented by its bottom ideal-sheaf
presentation. -/
noncomputable def wholeDegree
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L : X.Modules) [Invertible L] {d : ℕ}
    (hXdim : topologicalKrullDim X = d)
    [HasExt (Sheaf (Opens.grothendieckTopology
      (⊥ : X.IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})] : ℚ :=
  degree k f L (⊥ : X.IdealSheafData) (topologicalKrullDim_bot_eq X hXdim)

/-- Unfold `wholeDegree` to the degree of the bottom-ideal closed subscheme. -/
theorem wholeDegree_def
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L : X.Modules) [Invertible L] {d : ℕ}
    (hXdim : topologicalKrullDim X = d)
    [HasExt (Sheaf (Opens.grothendieckTopology
      (⊥ : X.IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})] :
    wholeDegree k f L hXdim =
      degree k f L (⊥ : X.IdealSheafData) (topologicalKrullDim_bot_eq X hXdim) := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
