module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Scalar
public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of scalars for ordinary DG base change

This file gives the concrete comparison behind the restriction-of-scalars square for base
change.  Its components are defined on homogeneous pure tensors, before passing to homotopy or
derived categories.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open ComplexShape DifferentialGradedCategory HomologicalComplex
open scoped DifferentialGradedCategory TensorProduct

namespace DifferentialGradedModule.BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {A : CochainDGAlgebra.{u, u} R}

/-- The right-factor map `S ⟶ A ⊗[R] S` used to forget a base-changed module to an
`S`-module. -/
abbrev coefficientMap (A : CochainDGAlgebra.{u, u} R) :
    CochainDGAlgebra.Hom (coefficients (R := R) (S := S)) (algebra (S := S) A) :=
  CochainDGAlgebra.Tensor.rightFactorHom A (coefficients (R := R) (S := S))

/-- The canonical map from the ground ring DGA to a cochain DGA. -/
abbrev groundMap (A : CochainDGAlgebra.{u, u} R) :
    CochainDGAlgebra.Hom (CochainDGAlgebra.ofAlgebra R R) A :=
  CochainDGAlgebra.Hom.fromBase A

/-- The extension bimodule for the coefficient map `R ⟶ S`, both regarded as degree-zero
cochain DGAs over `R`. -/
abbrev coefficientExtension :
    DifferentialGradedBimodule (CochainDGAlgebra.ofAlgebra R R)
      (coefficients (R := R) (S := S)) :=
  DifferentialGradedBimodule.ChangeOfRings.extension
    (groundMap (coefficients (R := R) (S := S)))

/-- The two canonical maps from the ground-ring DGA to `A ⊗[R] S` agree. -/
@[stacks 0BYZ "commutative DGA square underlying base change"]
theorem algebraMap_comp_groundMap (A : CochainDGAlgebra.{u, u} R) :
    CochainDGAlgebra.Hom.comp (algebraMap (S := S) A) (groundMap A) =
      CochainDGAlgebra.Hom.comp (coefficientMap (S := S) A)
        (groundMap (coefficients (R := R) (S := S))) := sorry

/-- Base change followed by restriction along `S ⟶ A ⊗[R] S`. -/
abbrev restrictedObj (M : DifferentialGradedModule A) :
    DifferentialGradedModule (coefficients (R := R) (S := S)) :=
  (coefficientMap (S := S) A).restrictModule (obj (S := S) M)

/-- Forgetting an `A`-module to `R` and then extending scalars from `R` to `S`. -/
abbrev extendedObj (M : DifferentialGradedModule A) :
    DifferentialGradedModule (coefficients (R := R) (S := S)) :=
  DifferentialGradedBimodule.Tensor.obj ((groundMap A).restrictModule M)
    (coefficientExtension (R := R) (S := S))

/-- The pure-tensor value of the comparison between the two ordinary scalar-change paths. -/
def restrictionComparisonPure (M : DifferentialGradedModule A)
    (p q : ℤ) (x : M.X p) (s : (coefficients (R := R) (S := S)).X q) :
    DifferentialGradedBimodule.Tensor.family ((groundMap A).restrictModule M)
      (coefficientExtension (R := R) (S := S)) (p + q) :=
  DifferentialGradedBimodule.Tensor.tmul ((groundMap A).restrictModule M)
    (coefficientExtension (R := R) (S := S)) x s

/-- The ordinary restriction comparison on one homogeneous tensor summand. -/
def restrictionComparisonComponent (M : DifferentialGradedModule A) (n p q : ℤ)
    (h : p + q = n) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
        ((coefficients (R := R) (S := S)).X q) ⟶
      (extendedObj (S := S) M).X n :=
  ModuleCat.TensorProduct.lift R
    (LinearMap.mk₂ R
      (fun x s ↦ cast (congrArg (fun k : ℤ ↦ ((extendedObj (S := S) M).X k : Type u)) h)
        (restrictionComparisonPure (S := S) M p q x s)) sorry sorry sorry sorry)

/-- The degreewise linear map underlying the ordinary restriction comparison. -/
def restrictionComparisonLinear (M : DifferentialGradedModule A) (n : ℤ) :
    (restrictedObj (S := S) M).X n →ₗ[R] (extendedObj (S := S) M).X n :=
  (mapBifunctorDesc
    (K₁ := M.toCochainComplex)
    (K₂ := (coefficients (R := R) (S := S)).toCochainComplex)
    (F := CochainDGAlgebra.Tensor.baseBifunctor (R := R))
    (c := ComplexShape.up ℤ)
    (fun p q h ↦ restrictionComparisonComponent (S := S) M n p q h)).hom

/-- The canonical ordinary comparison between the two paths in the scalar-restriction square. -/
@[stacks 0BYZ "ordinary restriction-of-scalars base-change comparison"]
def restrictionComparison (M : DifferentialGradedModule A) :
    restrictedObj (S := S) M ⟶ extendedObj (S := S) M where
  hom := restrictionComparisonLinear (S := S) M
  comm_d := sorry
  comm_smul := sorry

/-- The ordinary restriction comparison evaluates as the identity on homogeneous pure tensors. -/
@[simp]
theorem restrictionComparison_tmul (M : DifferentialGradedModule A)
    (p q : ℤ) (x : M.X p) (s : (coefficients (R := R) (S := S)).X q) :
    (restrictionComparison (S := S) M).hom (p + q)
        ((summandInclusion (S := S) M p q (p + q) rfl).hom (x ⊗ₜ[R] s)) =
      restrictionComparisonPure (S := S) M p q x s := sorry

/-- The ordinary comparison between the two scalar-change paths is invertible. -/
theorem restrictionComparison_isIso (M : DifferentialGradedModule A) :
    IsIso (restrictionComparison (S := S) M) := sorry

/-- The canonical ordinary isomorphism between the two scalar-change paths. -/
noncomputable def restrictionComparisonIso (M : DifferentialGradedModule A) :
    restrictedObj (S := S) M ≅ extendedObj (S := S) M :=
  @asIso _ _ _ _ (restrictionComparison (S := S) M)
    (restrictionComparison_isIso (S := S) M)

/-- The homotopy-level path obtained by base change and then restriction to the coefficient
DGA. -/
abbrev restrictedKFunctor (A : CochainDGAlgebra.{u, u} R) :=
  (dgFunctor (S := S) A).mapK ⋙
    (coefficientMap (S := S) A).restrictDgFunctor.mapK

/-- The homotopy-level path obtained by restriction to the ground ring and extension to the
coefficient DGA. -/
abbrev extendedKFunctor (A : CochainDGAlgebra.{u, u} R) :=
  (groundMap A).restrictDgFunctor.mapK ⋙
    (DifferentialGradedBimodule.Tensor.dgFunctor
      (coefficientExtension (R := R) (S := S))).mapK

/-- The component of the ordinary restriction comparison in the DG homotopy category. -/
noncomputable def restrictionComparisonKApp
    (M : K R (DifferentialGradedModule.{u, u} A)) :
    (restrictedKFunctor (S := S) A).obj M ≅ (extendedKFunctor (S := S) A).obj M :=
  (DifferentialGradedModule.toK (coefficients (R := R) (S := S))).mapIso
    (restrictionComparisonIso (S := S) M.obj)

/-- The two ordinary scalar-change paths are naturally isomorphic on DG homotopy categories. -/
@[stacks 0BYZ "ordinary restriction-of-scalars square"]
noncomputable def restrictionComparisonK (A : CochainDGAlgebra.{u, u} R) :
    restrictedKFunctor (S := S) A ≅ extendedKFunctor (S := S) A :=
  NatIso.ofComponents (restrictionComparisonKApp (S := S)) (fun _ ↦ sorry)

end DifferentialGradedModule.BaseChange
