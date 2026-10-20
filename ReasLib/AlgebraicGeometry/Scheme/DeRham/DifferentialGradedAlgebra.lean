/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CupProduct
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Monoid
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Mon

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj ComplexShape
open RingedSite.Hom SheafOfModules.RingedSite
open SheafOfModules.RingedSite.DeRham

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

open DerivedPushforward

variable {X S : Scheme.{u}} (p : X ⟶ S)
/-- The unit section of the relative de Rham algebra is compatible with restriction maps. -/
theorem deRhamOneSection_naturality
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ((RingedSpace.DeRham.term p.toLRSHom.toShHom 0).val.map i).hom
        (basic (RingedSpace.DeRham.structureMap p.toLRSHom.toShHom) 0 U 1
          (fun k ↦ Fin.elim0 k)) =
      basic (RingedSpace.DeRham.structureMap p.toLRSHom.toShHom) 0 V 1
        (fun k ↦ Fin.elim0 k) := sorry

/-- The unit global section of the degree-zero relative de Rham term. -/
noncomputable def deRhamOneSection :
    (RingedSpace.DeRham.term p.toLRSHom.toShHom 0).val.sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ basic (RingedSpace.DeRham.structureMap p.toLRSHom.toShHom) 0 U 1
      (fun k ↦ Fin.elim0 k))
    (fun {_ _} i ↦ deRhamOneSection_naturality p i)

/-- The unit of the extended relative de Rham complex in degree zero. -/
noncomputable def deRhamOne :
    𝟙_ (RingedSite.ModuleCat.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) ⟶
      (extendedDeRhamComplex p).X 0 :=
  (tensorUnitToUnitModule.{u, u, u} :
      𝟙_ (RingedSite.ModuleCat.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) ⟶
        _) ≫
    (RingedSpace.DeRham.term p.toLRSHom.toShHom 0).unitHomEquiv.symm
      (deRhamOneSection p) ≫
    eqToHom (RingedSpace.DeRham.complex_X p.toLRSHom.toShHom 0).symm ≫
    ((deRhamComplex p).extendXIso embeddingUpNat rfl).inv

/-- The homogeneous multiplication of the extended relative de Rham complex. -/
noncomputable abbrev deRhamMul (n m : ℤ) :=
  HomologicalComplex.Monoidal.tensorHomComponent (extendedWedge p) n m

/-- Associativity of the homogeneous extended de Rham wedge. -/
theorem deRhamMul_assoc (n m k : ℤ) :
    (α_ ((extendedDeRhamComplex p).X n) ((extendedDeRhamComplex p).X m)
          ((extendedDeRhamComplex p).X k)).hom ≫
        ((extendedDeRhamComplex p).X n ◁ deRhamMul p m k) ≫
        deRhamMul p n (m + k) =
      (deRhamMul p n m ▷ (extendedDeRhamComplex p).X k) ≫
        deRhamMul p (n + m) k ≫
        eqToHom (congrArg (extendedDeRhamComplex p).X (Int.add_assoc n m k)) := sorry

/-- The homogeneous extended de Rham unit is a left identity. -/
theorem deRhamOne_mul (n : ℤ) :
    (λ_ ((extendedDeRhamComplex p).X n)).hom =
      (deRhamOne p ▷ (extendedDeRhamComplex p).X n) ≫
        deRhamMul p 0 n ≫
        eqToHom (congrArg (extendedDeRhamComplex p).X (zero_add n)) := sorry

/-- The homogeneous extended de Rham unit is a right identity. -/
theorem deRhamMul_one (n : ℤ) :
    (ρ_ ((extendedDeRhamComplex p).X n)).hom =
      ((extendedDeRhamComplex p).X n ◁ deRhamOne p) ≫
        deRhamMul p n 0 ≫
        eqToHom (congrArg (extendedDeRhamComplex p).X (add_zero n)) := sorry

/-- The extended de Rham differential satisfies the graded Leibniz rule. -/
theorem deRham_d_mul (n m : ℤ) :
    deRhamMul p n m ≫ (extendedDeRhamComplex p).d (n + m) (n + m + 1) =
      (((extendedDeRhamComplex p).d n (n + 1)) ▷
          (extendedDeRhamComplex p).X m) ≫
          deRhamMul p (n + 1) m ≫
          eqToHom (congrArg (extendedDeRhamComplex p).X
            ((Int.add_assoc n 1 m).trans
              ((congrArg (fun a : ℤ ↦ n + a) (Int.add_comm 1 m)).trans
                (Int.add_assoc n m 1).symm))) +
        n.negOnePow •
          (((extendedDeRhamComplex p).X n ◁
              (extendedDeRhamComplex p).d m (m + 1)) ≫
            deRhamMul p n (m + 1) ≫
            eqToHom (congrArg (extendedDeRhamComplex p).X
              (Int.add_assoc n m 1).symm)) := sorry

/-- The canonical differential graded relative de Rham algebra on the integer-extended complex. -/
noncomputable def deRhamDGA :
    @DifferentialGradedAlgebra.{u, u, u}
      (Opens X) _ (Opens.grothendieckTopology X) _ _ _
      (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom) where
  toComplex := extendedDeRhamComplex p
  mul := deRhamMul p
  one := deRhamOne p
  mul_assoc := deRhamMul_assoc p
  one_mul := deRhamOne_mul p
  mul_one := deRhamMul_one p
  d_mul := deRham_d_mul p

/-- The canonical de Rham DGA has the integer-extended relative de Rham complex as its carrier. -/
theorem deRhamDGA_toComplex : (deRhamDGA p).toComplex = extendedDeRhamComplex p := sorry

/-- The multiplication of the canonical de Rham DGA is induced by `extendedWedge`. -/
theorem deRhamDGA_mul (n m : ℤ) :
    (deRhamDGA p).mul n m =
      HomologicalComplex.Monoidal.tensorHomComponent (extendedWedge p) n m := sorry

-- Local instance justification (defeq pin): the conditional localization formulas use the canonical coefficient-site derived category already fixed by moduleLocalization.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable [moduleDerivedMonoidalP : MonoidalCategory
  (ModuleDerived.{u, u, u, u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))]
variable [localizationLaxMonoidal : Functor.LaxMonoidal
  (moduleLocalization.{u, u, u, u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))]

/-- The wedge multiplication transported first to the homotopy category and then to the
derived category of modules over `p⁻¹ᴼᵏ_S`. -/
noncomputable def derivedDeRhamMultiplication :
    derivedComplex p ⊗ derivedComplex p ⟶ derivedComplex p :=
  @Functor.LaxMonoidal.μ _ _ _ _ _ _
      (moduleLocalization.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      localizationLaxMonoidal
      ((HomotopyCategory.quotient
        (RingedSite.ModuleCat.{u, u, u, u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
        (up ℤ)).obj (extendedDeRhamComplex p))
      ((HomotopyCategory.quotient
        (RingedSite.ModuleCat.{u, u, u, u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
        (up ℤ)).obj (extendedDeRhamComplex p)) ≫
    (moduleLocalization.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).map
        (Functor.LaxMonoidal.μ
            (HomotopyCategory.quotient
              (RingedSite.ModuleCat.{u, u, u, u}
                (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
              (up ℤ))
            (extendedDeRhamComplex p) (extendedDeRhamComplex p) ≫
          (HomotopyCategory.quotient
            (RingedSite.ModuleCat.{u, u, u, u}
              (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
            (up ℤ)).map (extendedWedge p))

/-- The multiplication on `derivedComplex p` is the image of `extendedWedge` through the two
lax-monoidal localization functors. -/
theorem derivedDeRhamMultiplication_eq :
    derivedDeRhamMultiplication p =
      @Functor.LaxMonoidal.μ _ _ _ _ _ _
          (moduleLocalization.{u, u, u, u}
            (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
          localizationLaxMonoidal
          ((HomotopyCategory.quotient
            (RingedSite.ModuleCat.{u, u, u, u}
              (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
            (up ℤ)).obj (extendedDeRhamComplex p))
          ((HomotopyCategory.quotient
            (RingedSite.ModuleCat.{u, u, u, u}
              (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
            (up ℤ)).obj (extendedDeRhamComplex p)) ≫
        (moduleLocalization.{u, u, u, u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).map
            (Functor.LaxMonoidal.μ
                (HomotopyCategory.quotient
                  (RingedSite.ModuleCat.{u, u, u, u}
                    (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
                  (up ℤ))
                (extendedDeRhamComplex p) (extendedDeRhamComplex p) ≫
              (HomotopyCategory.quotient
                (RingedSite.ModuleCat.{u, u, u, u}
                  (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
                (up ℤ)).map (extendedWedge p)) := sorry

end AlgebraicGeometry.Scheme.DeRham
