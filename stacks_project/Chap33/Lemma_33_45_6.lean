module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Components
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

universe u v

/- Lemma 33.45.6: in the situation of Definition 33.45.3, the intersection number of a
`d`-dimensional closed subscheme is the multiplicity-weighted sum of the intersection numbers of
its `d`-dimensional irreducible components. -/
@[stacks 0BES] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.number_eq_sum_irreducibleComponents :
    ∀ {k : Type u} [Field k]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      {d : ℕ} (hZdim : topologicalKrullDim Z.subscheme = d)
      (L : Fin d → X.Modules) [∀ j : Fin d, Scheme.Modules.Invertible (L j)]
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
              (ξ i)) = m i),
      Scheme.Modules.Intersection.number k f Z hZdim L =
        ∑ i : ι, (m i : ℚ) *
          Scheme.Modules.Intersection.number k f (Zi i) (h_component_topDim i) L)
