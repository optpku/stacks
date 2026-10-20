/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CupProduct
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open SheafOfModules SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- Naturality of the unit section used in the relative de Rham DGA. -/
theorem gaussManinDeRhamOneSection_naturality {Y S : Scheme.{u}}
    (b : Y ⟶ S) {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    ((RingedSpace.DeRham.term b.toLRSHom.toShHom 0).val.map i).hom
        (RingedSite.DeRham.basic
          (RingedSpace.DeRham.structureMap b.toLRSHom.toShHom) 0 U 1
          (fun k ↦ Fin.elim0 k)) =
      RingedSite.DeRham.basic
        (RingedSpace.DeRham.structureMap b.toLRSHom.toShHom) 0 V 1
        (fun k ↦ Fin.elim0 k) := sorry

/-- The canonical global unit section of the relative de Rham DGA. -/
noncomputable def gaussManinDeRhamOneSection {Y S : Scheme.{u}}
    (b : Y ⟶ S) :
    (RingedSpace.DeRham.term b.toLRSHom.toShHom 0).val.sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ RingedSite.DeRham.basic
      (RingedSpace.DeRham.structureMap b.toLRSHom.toShHom) 0 U 1
      (fun k ↦ Fin.elim0 k))
    (fun {_ _} i ↦ gaussManinDeRhamOneSection_naturality b i)

/-- The unit of the integer-extended relative de Rham complex. -/
noncomputable def gaussManinDeRhamOne {Y S : Scheme.{u}}
    (b : Y ⟶ S) :
    𝟙_ (RingedSite.ModuleCat.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)) ⟶
      (extendedDeRhamComplex b).X 0 :=
  (tensorUnitToUnitModule.{u, u, u} :
      𝟙_ (RingedSite.ModuleCat.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)) ⟶ _) ≫
    (RingedSpace.DeRham.term b.toLRSHom.toShHom 0).unitHomEquiv.symm
      (gaussManinDeRhamOneSection b) ≫
    eqToHom (RingedSpace.DeRham.complex_X b.toLRSHom.toShHom 0).symm ≫
    ((deRhamComplex b).extendXIso embeddingUpNat rfl).inv

/-- Homogeneous multiplication on the extended relative de Rham complex. -/
noncomputable abbrev gaussManinDeRhamMul {Y S : Scheme.{u}}
    (b : Y ⟶ S) (n m : ℤ) :=
  HomologicalComplex.Monoidal.tensorHomComponent (extendedWedge b) n m

/-- Associativity of the homogeneous relative de Rham multiplication. -/
theorem gaussManinDeRhamMul_assoc {Y S : Scheme.{u}}
    (b : Y ⟶ S) (n m k : ℤ) :
    (α_ ((extendedDeRhamComplex b).X n) ((extendedDeRhamComplex b).X m)
          ((extendedDeRhamComplex b).X k)).hom ≫
        ((extendedDeRhamComplex b).X n ◁ gaussManinDeRhamMul b m k) ≫
        gaussManinDeRhamMul b n (m + k) =
      (gaussManinDeRhamMul b n m ▷ (extendedDeRhamComplex b).X k) ≫
        gaussManinDeRhamMul b (n + m) k ≫
        eqToHom (congrArg (extendedDeRhamComplex b).X (Int.add_assoc n m k)) := sorry

/-- The relative de Rham unit is a left identity. -/
theorem gaussManinDeRhamOne_mul {Y S : Scheme.{u}}
    (b : Y ⟶ S) (n : ℤ) :
    (λ_ ((extendedDeRhamComplex b).X n)).hom =
      (gaussManinDeRhamOne b ▷ (extendedDeRhamComplex b).X n) ≫
        gaussManinDeRhamMul b 0 n ≫
        eqToHom (congrArg (extendedDeRhamComplex b).X (zero_add n)) := sorry

/-- The relative de Rham unit is a right identity. -/
theorem gaussManinDeRhamMul_one {Y S : Scheme.{u}}
    (b : Y ⟶ S) (n : ℤ) :
    (ρ_ ((extendedDeRhamComplex b).X n)).hom =
      ((extendedDeRhamComplex b).X n ◁ gaussManinDeRhamOne b) ≫
        gaussManinDeRhamMul b n 0 ≫
        eqToHom (congrArg (extendedDeRhamComplex b).X (add_zero n)) := sorry

/-- The relative de Rham differential satisfies the graded Leibniz rule. -/
theorem gaussManinDeRham_d_mul {Y S : Scheme.{u}}
    (b : Y ⟶ S) (n m : ℤ) :
    gaussManinDeRhamMul b n m ≫
        (extendedDeRhamComplex b).d (n + m) (n + m + 1) =
      (((extendedDeRhamComplex b).d n (n + 1)) ▷
          (extendedDeRhamComplex b).X m) ≫
          gaussManinDeRhamMul b (n + 1) m ≫
          eqToHom (congrArg (extendedDeRhamComplex b).X
            ((Int.add_assoc n 1 m).trans
              ((congrArg (fun a : ℤ ↦ n + a) (Int.add_comm 1 m)).trans
                (Int.add_assoc n m 1).symm))) +
        n.negOnePow •
          (((extendedDeRhamComplex b).X n ◁
              (extendedDeRhamComplex b).d m (m + 1)) ≫
            gaussManinDeRhamMul b n (m + 1) ≫
            eqToHom (congrArg (extendedDeRhamComplex b).X
              (Int.add_assoc n m 1).symm)) := sorry

/-- The canonical relative de Rham DGA used by the Gauss–Manin construction. -/
noncomputable def gaussManinDeRhamDGA {Y S : Scheme.{u}} (b : Y ⟶ S) :
    @DifferentialGradedAlgebra.{u, u, u} _ _ (Opens.grothendieckTopology Y)
      _ _ _ (RingedSpace.DeRham.coefficients b.toLRSHom.toShHom) where
  toComplex := extendedDeRhamComplex b
  mul := gaussManinDeRhamMul b
  one := gaussManinDeRhamOne b
  mul_assoc := gaussManinDeRhamMul_assoc b
  one_mul := gaussManinDeRhamOne_mul b
  mul_one := gaussManinDeRhamMul_one b
  d_mul := gaussManinDeRham_d_mul b

/-- The relative de Rham DGA has the extended de Rham complex as carrier. -/
theorem gaussManinDeRhamDGA_toComplex {Y S : Scheme.{u}} (b : Y ⟶ S) :
    (gaussManinDeRhamDGA b).toComplex = extendedDeRhamComplex b := sorry

end AlgebraicGeometry.Scheme.DeRham

