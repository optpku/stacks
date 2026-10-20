module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/-
Definition 33.45.3 defines the intersection number of invertible modules with a
closed subscheme as the multilinear coefficient of its twist Euler
characteristic polynomial.
-/
@[stacks 0BEP] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.number :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ}
      (hZdim : topologicalKrullDim Z.subscheme = d)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (L : Fin d → X.Modules)
      [∀ j : Fin d, AlgebraicGeometry.Scheme.Modules.Invertible (L j)],
      ℚ)

#check
  (AlgebraicGeometry.Scheme.Modules.Intersection.number_eq_coeff :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ}
      (hZdim : topologicalKrullDim Z.subscheme = d)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (L : Fin d → X.Modules)
      [∀ j : Fin d, AlgebraicGeometry.Scheme.Modules.Invertible (L j)]
      {P : MvPolynomial (Fin d) ℚ}
      (hP : ∀ n : Fin d → ℤ,
        MvPolynomial.eval (fun j : Fin d ↦ (n j : ℚ)) P =
          (AlgebraicGeometry.Scheme.Modules.Intersection.eulerCharacteristic k f Z L n : ℚ)),
      AlgebraicGeometry.Scheme.Modules.Intersection.number k f Z hZdim L =
        P.coeff (AlgebraicGeometry.Scheme.Modules.Intersection.multilinearExponent d))

#check
  (AlgebraicGeometry.Scheme.Modules.Intersection.eulerCharacteristic_pushforwardStructureTwist_eq :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (L : Fin d → X.Modules)
      [∀ j : Fin d, AlgebraicGeometry.Scheme.Modules.Invertible (L j)]
      (n : Fin d → ℤ),
      Scheme.Hom.eulerCharacteristic f
          (AlgebraicGeometry.Scheme.Modules.Intersection.pushforwardStructureTwist k f Z L n) =
        AlgebraicGeometry.Scheme.Modules.Intersection.eulerCharacteristic k f Z L n)

#check
  (AlgebraicGeometry.Scheme.Modules.Intersection.selfNumber :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ}
      (hZdim : topologicalKrullDim Z.subscheme = d)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L],
      ℚ)

#check
  (AlgebraicGeometry.Scheme.Modules.Intersection.selfNumber_def :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ}
      (hZdim : topologicalKrullDim Z.subscheme = d)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L],
      AlgebraicGeometry.Scheme.Modules.Intersection.selfNumber k f Z hZdim L =
        AlgebraicGeometry.Scheme.Modules.Intersection.number k f Z hZdim (fun _ ↦ L))
