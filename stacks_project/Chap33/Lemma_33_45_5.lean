module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Additivity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.45.5: in the situation of Definition 33.45.3, the intersection number is additive in
one factor. If `L i ≅ tensorObj L' L''`, then
`(L₁ ⋯ L_i ⋯ L_d · Z) = (L₁ ⋯ L_i' ⋯ L_d · Z) + (L₁ ⋯ L_i'' ⋯ L_d · Z)`. -/
@[stacks 0BER] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.number_eq_add_of_iso_tensorObj :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ}
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (hZdim : topologicalKrullDim Z.subscheme = d)
      (L : Fin d → X.Modules)
      [∀ j : Fin d, AlgebraicGeometry.Scheme.Modules.Invertible (L j)]
      (i : Fin d) (L' L'' : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L']
      [AlgebraicGeometry.Scheme.Modules.Invertible L'']
      (hTensor : L i ≅ tensorObj L' L''),
      AlgebraicGeometry.Scheme.Modules.Intersection.number k f Z hZdim L =
        AlgebraicGeometry.Scheme.Modules.Intersection.number k f Z hZdim
          (Function.update L i L') +
          AlgebraicGeometry.Scheme.Modules.Intersection.number k f Z hZdim
            (Function.update L i L''))
