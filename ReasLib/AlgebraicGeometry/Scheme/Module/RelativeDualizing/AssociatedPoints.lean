/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locus.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite SheafOfModules
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

/-- If the flat locus of a quasi-finite morphism of Noetherian schemes contains the associated
points of the source and the inverse image of the associated points of the target, then it contains
the associated points of the relative dualizing sheaf. -/
theorem associatedPoints_subset_flatOpen
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf) (V : Y.Opens)
    (hV : (V : Set Y) = {y : Y | f.flatAt y})
    (h_source : Y.associatedPoints ⊆ (V : Set Y))
    (h_target : (fun y : Y ↦ f y) ⁻¹' X.associatedPoints ⊆ (V : Set Y)) :
    Scheme.Modules.associatedPoints W.module.obj ⊆ (V : Set Y) := sorry

/-- Two global sections of a relative dualizing sheaf that restrict to the same section of the
flat locus are equal, when that locus contains the associated points of the structure sheaves of
the source and target in the sense required for the dualizing sheaf. -/
theorem sections_eq_of_restrict_eq
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf) (V : Y.Opens)
    (hV : (V : Set Y) = {y : Y | f.flatAt y})
    (h_source : Y.associatedPoints ⊆ (V : Set Y))
    (h_target : (fun y : Y ↦ f y) ⁻¹' X.associatedPoints ⊆ (V : Set Y))
    (τV : Γ(W.module.obj, V)) (τ₁ τ₂ : sections W.module.obj)
    (h_τ₁ : τ₁.1 (op V) = τV) (h_τ₂ : τ₂.1 (op V) = τV) :
    τ₁ = τ₂ := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf
