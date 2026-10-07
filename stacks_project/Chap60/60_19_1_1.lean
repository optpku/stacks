module

import ReasLib.AlgebraicTopology.CosimplicialObject.VertexModule
import StacksCheckRecall

open CategoryTheory Opposite
open scoped Simplicial

universe u

/- 60.19.1.1: `hom` evaluates to the prescribed cutoff formula, and checking
all coordinates gives the displayed naturality equation for the free vertex
modules. -/
@[stacks 07L8] #check
  (CategoryTheory.CosimplicialObject.VertexModule.hom_naturality :
    ∀ (A : CosimplicialObject RingCat.{u}) {n m : SimplexCategory} (f : n ⟶ m)
      (x : Fin (n.len + 1) →₀ A.obj n)
      (α : (Δ[1] : SSet.{0}).obj (op m)),
      CategoryTheory.CosimplicialObject.VertexModule.hom A m
          (CategoryTheory.CosimplicialObject.VertexModule.map A f x) α =
        CategoryTheory.CosimplicialObject.VertexModule.map A f
          (CategoryTheory.CosimplicialObject.VertexModule.hom A n x
            ((Δ[1] : SSet.{0}).map f.op α)))
