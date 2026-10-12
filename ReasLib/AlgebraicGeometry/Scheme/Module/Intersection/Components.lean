/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic.Components
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number

/-!
# Intersection numbers and irreducible components

This file records the decomposition of an intersection number into the contributions of the
top-dimensional irreducible components of a closed subscheme.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- The intersection number of a closed subscheme proper over a field is the
multiplicity-weighted sum of the intersection numbers of an explicit finite, injective, and
exhaustive family of its top-dimensional integral components. Each multiplicity is the length of
the stalk of the pushed-forward structure module at the corresponding generic point. -/
theorem number_eq_sum_irreducibleComponents
    {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    {d : ℕ} (hZdim : topologicalKrullDim Z.subscheme = d)
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    {ι : Type v} [Fintype ι]
    (ξ : ι → X)
    (Zi : ι → X.IdealSheafData)
    [∀ i : ι,
      HasExt (Sheaf (Opens.grothendieckTopology (Zi i).subscheme.carrier) AddCommGrpCat.{u})]
    (h_integral : ∀ i, IsIntegral (Zi i).subscheme)
    (h_component_mem :
      ∀ i, ξ i ∈ X.minimalSpecializationPoints (Z.support : Set X))
    (h_component_generic :
      ∀ i, IsGenericPoint (ξ i) ((Zi i).support : Set X))
    (h_component_topDim :
      ∀ i, topologicalKrullDim (Zi i).subscheme = d)
    (h_exhaustive :
      ∀ x : X,
        x ∈ X.minimalSpecializationPoints (Z.support : Set X) →
          topologicalKrullDim (closure ({x} : Set X)) = d →
            ∃ i, ξ i = x)
    (h_injective : Function.Injective ξ)
    (m : ι → ℕ)
    (h_length :
      ∀ i,
        Module.length (X.presheaf.stalk (ξ i))
          (RingedSpace.stalkModuleCat
            ((Scheme.Modules.pushforward Z.subschemeι).obj
              (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules))
            (ξ i)) = m i) :
    Intersection.number k f Z hZdim L =
      ∑ i : ι, (m i : ℚ) * Intersection.number k f (Zi i) (h_component_topDim i) L := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
