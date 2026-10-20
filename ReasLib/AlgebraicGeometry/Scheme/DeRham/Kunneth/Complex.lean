/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.Embedding.Functor
public import ReasLib.Algebra.Homology.Embedding.UpNatMonoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.DifferentialOperator
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.Coefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Kunneth

variable {S X : Scheme.{u}}

/-- Relative differential forms on a scheme are quasicoherent. -/
instance formIsQuasicoherent (a : X ⟶ S) (n : ℕ) :
    (RingedSpace.DeRham.form.{u} a.toLRSHom.toShHom n).IsQuasicoherent := sorry

/-- A relative differential-form sheaf as an object of the quasicoherent category. -/
abbrev formQCoh (a : X ⟶ S) (n : ℕ) : Scheme.QCoh X :=
  ⟨RingedSpace.DeRham.form.{u} a.toLRSHom.toShHom n, formIsQuasicoherent a n⟩

/-- A relative differential-form sheaf as an object of the category whose morphisms are
finite-order differential operators over the base. -/
abbrev operatorForm (a : X ⟶ S) (n : ℕ) :
    Scheme.Hom.FiniteOrderDifferentialOperatorCat a :=
  Scheme.Hom.FiniteOrderDifferentialOperatorCat.ofQCoh a (formQCoh a n)

/-- The de Rham differential transported to the underlying modules of the bundled
quasicoherent forms. -/
noncomputable def operatorDifferentialHom (a : X ⟶ S) (n : ℕ) :
    (restrictionAlong
      (Scheme.Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)).obj
        (Scheme.Hom.FiniteOrderDifferentialOperatorCat.underlying a (operatorForm a n)) ⟶
      (restrictionAlong
        (Scheme.Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)).obj
          (Scheme.Hom.FiniteOrderDifferentialOperatorCat.underlying a
            (operatorForm a (n + 1))) :=
  (restrictionAlong
      (Scheme.Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)).map
        (eqToHom (Scheme.Hom.FiniteOrderDifferentialOperatorCat.underlying_ofQCoh
          a (formQCoh a n))) ≫
    RingedSpace.DeRham.d.{u} a.toLRSHom.toShHom n ≫
    (restrictionAlong
      (Scheme.Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)).map
        (eqToHom (Scheme.Hom.FiniteOrderDifferentialOperatorCat.underlying_ofQCoh
          a (formQCoh a (n + 1))).symm)

/-- The transported relative de Rham differential has order at most one over the base. -/
theorem operatorDifferentialHom_isOrderOne (a : X ⟶ S) (n : ℕ) :
    SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder
      (J := Opens.grothendieckTopology X)
      (Scheme.Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)
      (operatorDifferentialHom a n) 1 := sorry

/-- The de Rham differential bundled as a finite-order differential operator. -/
noncomputable def operatorDifferential (a : X ⟶ S) (n : ℕ) :
    operatorForm a n ⟶ operatorForm a (n + 1) :=
  DifferentialOperators.FiniteOrder.ofOrder
    (φ := Scheme.Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)
    (F := Scheme.Hom.FiniteOrderDifferentialOperatorCat.underlying a (operatorForm a n))
    (G := Scheme.Hom.FiniteOrderDifferentialOperatorCat.underlying a
      (operatorForm a (n + 1)))
    (DifferentialOperators.ofHom.{u, u, u, u} (operatorDifferentialHom a n)
      (operatorDifferentialHom_isOrderOne a n))

/-- Consecutive bundled de Rham differential operators compose to zero. -/
theorem operatorDifferential_comp (a : X ⟶ S) (n : ℕ) :
    operatorDifferential a n ≫ operatorDifferential a (n + 1) = 0 := sorry

/-- The relative de Rham complex in the category of quasicoherent modules and finite-order
differential operators over the base. -/
noncomputable def operatorComplex (a : X ⟶ S) :
    CochainComplex (Scheme.Hom.FiniteOrderDifferentialOperatorCat a) ℕ :=
  CochainComplex.of (operatorForm a) (operatorDifferential a)
    (operatorDifferential_comp a)

/-- The relative differential-operator de Rham complex extended from `ℕ` to `ℤ`. -/
noncomputable abbrev extendedOperatorComplex (a : X ⟶ S) :
    CochainComplex (Scheme.Hom.FiniteOrderDifferentialOperatorCat a) ℤ :=
  (operatorComplex a).extend embeddingUpNat

/-- The coefficient realization of an operator-valued de Rham term is canonically the
corresponding term of the usual relative de Rham complex. -/
noncomputable def operatorDeRhamComponentIso (a : X ⟶ S) (n : ℕ) :
    (Scheme.Hom.FiniteOrderDifferentialOperatorCat.toCoefficientModules a).obj
        ((operatorComplex a).X n) ≅
      (RingedSpace.DeRham.complex a.toLRSHom.toShHom).X n :=
  (restrictionAlong
    (Scheme.Hom.FiniteOrderDifferentialOperatorCat.coefficientMap a)).mapIso
      (eqToIso (Scheme.Hom.FiniteOrderDifferentialOperatorCat.underlying_ofQCoh
        a (formQCoh a n)))

/-- The coefficient-term identifications commute with the relative de Rham differentials. -/
theorem operatorDeRhamComponentIso_comm (a : X ⟶ S) (i j : ℕ)
    (hij : (up ℕ).Rel i j) :
    (operatorDeRhamComponentIso a i).hom ≫
        (RingedSpace.DeRham.complex a.toLRSHom.toShHom).d i j =
      ((Scheme.Hom.FiniteOrderDifferentialOperatorCat.toCoefficientModules a
        |>.mapHomologicalComplex (up ℕ)).obj (operatorComplex a)).d i j ≫
        (operatorDeRhamComponentIso a j).hom := sorry

/-- Coefficient realization identifies the nonnegative operator de Rham complex with the
usual relative de Rham complex. -/
noncomputable def operatorDeRhamIsoNat (a : X ⟶ S) :
    (Scheme.Hom.FiniteOrderDifferentialOperatorCat.toCoefficientModules a
      |>.mapHomologicalComplex (up ℕ)).obj (operatorComplex a) ≅
        RingedSpace.DeRham.complex a.toLRSHom.toShHom :=
  HomologicalComplex.Hom.isoOfComponents (operatorDeRhamComponentIso a)
    (operatorDeRhamComponentIso_comm a)

/-- Coefficient realization identifies the extended operator de Rham complex with the
standard relative de Rham complex extended from `ℕ` to `ℤ`. -/
noncomputable def operatorDeRhamIso (a : X ⟶ S) :
    (Scheme.Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex a).obj
        (extendedOperatorComplex a) ≅
      (RingedSpace.DeRham.complex a.toLRSHom.toShHom).extend embeddingUpNat :=
  embeddingUpNat.mapAppIso
      (Scheme.Hom.FiniteOrderDifferentialOperatorCat.toCoefficientModules a)
      (operatorComplex a) ≪≫
    (embeddingUpNat.extendFunctor _).mapIso (operatorDeRhamIsoNat a)

/-- The forward map of `operatorDeRhamIso` is extension-change comparison followed by the
extended degreewise coefficient identification. -/
theorem operatorDeRhamIso_hom (a : X ⟶ S) :
    (operatorDeRhamIso a).hom =
      (embeddingUpNat.mapAppIso
        (Scheme.Hom.FiniteOrderDifferentialOperatorCat.toCoefficientModules a)
        (operatorComplex a)).hom ≫
        (embeddingUpNat.extendFunctor _).map (operatorDeRhamIsoNat a).hom := sorry

end AlgebraicGeometry.Scheme.DeRham.Kunneth
