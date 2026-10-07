module

public import stacks_project.Chap96.Definition_96_26_1_Affine
public import stacks_project.Chap96.Definition_96_26_1_QC
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver
open CategoryTheory.ModulesOnCategory

universe u

/- Definition 96.26.1: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. Let `𝒪` be the sheaf of rings on `𝒳_affine`. We define the
triangulated category of quasi-coherent objects in the derived category by
the formula `QC(𝒳) = QC(𝒳_affine, 𝒪)`, where the right-hand side is
Cohomology on Sites, Definition 21.43.1. -/
@[stacks 0H0H] #check (fun {S : Scheme.{u}} (X : GroupoidsOver S) ↦ QC X)

/- The restricted structure sheaf `𝒪` on the chaotic affine site `𝒳_affine`. -/
#check (fun {S : Scheme.{u}} (X : GroupoidsOver S) ↦ affineStructureSheaf X)

/- The comparison-map category `QC(𝒳_affine, 𝒪)` of Definition 21.43.1. -/
#check
  (fun {S : Scheme.{u}} (X : GroupoidsOver S) ↦
    Chaotic.QC.{u + 1, u, u} (affineStructureSheaf X))
