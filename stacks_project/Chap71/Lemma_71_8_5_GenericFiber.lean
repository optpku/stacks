module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_1_Product

/-!
# Generic fibers of algebraic spaces over affine bases

The fibre product `Spec K ×_{Spec R} X` of an algebraic space `X` over `Spec R`
along an algebra map `R → K` is the chosen representative of the generic fiber
`X_K`, with projections to `X` and to `Spec K`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GenericFiber

/-- The algebraic space `Spec K` over `Spec R` associated to a commutative algebra
`K` over `R`. -/
abbrev specOver (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] :
    AlgebraicSpace (Spec (CommRingCat.of R)) :=
  ofOver (Over.mk (Scheme.AffineBaseChange.specMap R K))

/-- `specOver R K` is the represented algebraic space of `Spec K ⟶ Spec R`. -/
theorem specOver_eq (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] :
    specOver R K = ofOver (Over.mk (Scheme.AffineBaseChange.specMap R K)) :=
  sorry

/-- The base change of an algebraic space `X` over `Spec R` along `Spec K ⟶ Spec R`,
as the fibre product `Spec K ×_{Spec R} X` in algebraic spaces over `Spec R`. -/
abbrev baseChange (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (X : AlgebraicSpace (Spec (CommRingCat.of R))) :
    AlgebraicSpace (Spec (CommRingCat.of R)) :=
  product (specOver R K) X

/-- The generic-fiber base change is the slice product with `specOver R K`. -/
theorem baseChange_eq (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (X : AlgebraicSpace (Spec (CommRingCat.of R))) :
    baseChange R K X = product (specOver R K) X :=
  sorry

/-- The projection from the generic-fiber base change back to `X`. -/
abbrev toSource (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (X : AlgebraicSpace (Spec (CommRingCat.of R))) :
    baseChange R K X ⟶ X :=
  productSnd (specOver R K) X

/-- The source projection of a generic-fiber base change is the second product
projection. -/
theorem toSource_eq (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (X : AlgebraicSpace (Spec (CommRingCat.of R))) :
    toSource R K X = productSnd (specOver R K) X :=
  sorry

/-- The projection from the generic-fiber base change to `Spec K` over `Spec R`. -/
abbrev toBase (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (X : AlgebraicSpace (Spec (CommRingCat.of R))) :
    baseChange R K X ⟶ specOver R K :=
  productFst (specOver R K) X

/-- The base projection of a generic-fiber base change is the first product
projection. -/
theorem toBase_eq (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (X : AlgebraicSpace (Spec (CommRingCat.of R))) :
    toBase R K X = productFst (specOver R K) X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GenericFiber
