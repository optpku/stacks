module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.QuasiCoherent
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
@[stacks 0H0H] #check (AlgebraicGeometry.GroupoidsOver.QC :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    Type (u + 2))

/- The restricted structure sheaf `𝒪` on the chaotic affine site `𝒳_affine`. -/
#check (AlgebraicGeometry.GroupoidsOver.affineStructureSheaf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    Sheaf (⊥ : GrothendieckTopology (affineSite X)) CommRingCat.{u + 1})

/- The comparison-map category `QC(𝒳_affine, 𝒪)` of Definition 21.43.1. -/
#check (AlgebraicGeometry.GroupoidsOver.QC_eq :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    QC X = Chaotic.QC.{u + 1, u, u} (affineStructureSheaf X))
