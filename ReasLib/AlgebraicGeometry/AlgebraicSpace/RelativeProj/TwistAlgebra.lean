/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Triple

/-! # Integer-graded twist families and algebra comparisons -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- The unlifted Serre twist family `⊕_d 𝒪_P(d)` on a fixed algebraic space. -/
structure TwistFamily {S : Scheme.{u}} (P : AlgebraicSpace S) where
  /-- The `ℤ`-graded algebra sheaf whose degree-`n` piece is `𝒪_P(n)`. -/
  algebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift P)
  /-- The unlifted family of twist modules `𝒪_P(n)`. -/
  obj : ℤ → P.Modules
  /-- Universe lift identifies `𝒪_P(n)` with the degree-`n` piece of the twist algebra. -/
  iso : ∀ n : ℤ, Modules.liftModule (obj n) ≅ algebra.obj n
  /-- Unlifted multiplication of twists. -/
  mul : ∀ n m : ℤ, obj n ⊗ obj m ⟶ obj (n + m)
  /-- The unlifted degree-zero unit. -/
  unit : SheafOfModules.unit (structureSheaf P) ⟶ obj 0
  /-- The unit is the actual unit of the displayed graded algebra after universe transport. -/
  unit_spec :
    (Modules.liftedUnitIso P).inv ≫ Modules.liftModuleMap unit ≫ (iso 0).hom =
      gradedOneHom algebra
  /-- Multiplication agrees with the displayed graded algebra after universe transport. -/
  mul_spec : ∀ n m : ℤ,
    liftModuleTensorHom (obj n) (obj m) ≫ Modules.liftModuleMap (mul n m) =
      ((iso n).hom ⊗ₘ (iso m).hom) ≫ GradedAlgebraSheaf.mulHom algebra n m ≫
        (iso (n + m)).inv

namespace TwistFamily

variable {S : Scheme.{u}} {P : AlgebraicSpace S}

/-- Construct a twist family from its algebra, unlifted modules, comparison isomorphisms,
multiplication, and unit. -/
def of (algebra : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift P))
    (obj : ℤ → P.Modules)
    (iso : ∀ n : ℤ, Modules.liftModule (obj n) ≅ algebra.obj n)
    (mul : ∀ n m : ℤ, obj n ⊗ obj m ⟶ obj (n + m))
    (unit : SheafOfModules.unit (structureSheaf P) ⟶ obj 0)
    (unit_spec :
      (Modules.liftedUnitIso P).inv ≫ Modules.liftModuleMap unit ≫ (iso 0).hom =
        gradedOneHom algebra)
    (mul_spec : ∀ n m : ℤ,
      liftModuleTensorHom (obj n) (obj m) ≫ Modules.liftModuleMap (mul n m) =
        ((iso n).hom ⊗ₘ (iso m).hom) ≫ GradedAlgebraSheaf.mulHom algebra n m ≫
          (iso (n + m)).inv) :
    TwistFamily P where
  algebra := algebra
  obj := obj
  iso := iso
  mul := mul
  unit := unit
  unit_spec := unit_spec
  mul_spec := mul_spec



/-- The unit and multiplication of a twist family agree with its graded algebra. -/
theorem conditions_spec (A : TwistFamily P) :
    ((Modules.liftedUnitIso P).inv ≫ Modules.liftModuleMap A.unit ≫ (A.iso 0).hom =
      gradedOneHom A.algebra) ∧
    ∀ n m : ℤ,
      liftModuleTensorHom (A.obj n) (A.obj m) ≫ Modules.liftModuleMap (A.mul n m) =
        ((A.iso n).hom ⊗ₘ (A.iso m).hom) ≫ GradedAlgebraSheaf.mulHom A.algebra n m ≫
          (A.iso (n + m)).inv := sorry

end TwistFamily

/-- A graded-algebra comparison along a morphism of algebraic spaces: degreewise module maps
together with unit and multiplication preservation. -/
structure GradedAlgebraComparison {S : Scheme.{u}} {Y Y' : AlgebraicSpace S} (f : Y' ⟶ Y)
    (A : TwistFamily Y) (A' : TwistFamily Y') where
  /-- The degreewise comparison from the pullback of `A` to `A'`. -/
  degreeMap : ∀ n : ℤ, (Modules.pullback f).obj (A.obj n) ⟶ A'.obj n
  /-- The degree-zero unit is preserved. -/
  map_one :
    Modules.structureModulePullbackInv f ≫
        (Modules.pullback f).map A.unit ≫ degreeMap 0 =
      A'.unit
  /-- Homogeneous multiplication is preserved. -/
  map_mul :
    ∀ n m : ℤ,
      pullbackTensorLax f (A.obj n) (A.obj m) ≫
          (Modules.pullback f).map (A.mul n m) ≫ degreeMap (n + m) =
        tensorHom (degreeMap n) (degreeMap m) ≫ A'.mul n m

namespace GradedAlgebraComparison

variable {S : Scheme.{u}} {Y Y' : AlgebraicSpace S} {f : Y' ⟶ Y}
variable {A : TwistFamily Y} {A' : TwistFamily Y'}

/-- Construct a graded-algebra comparison from its degree maps and algebra laws. -/
def of (degreeMap : ∀ n : ℤ, (Modules.pullback f).obj (A.obj n) ⟶ A'.obj n)
    (map_one :
      Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map A.unit ≫ degreeMap 0 = A'.unit)
    (map_mul : ∀ n m : ℤ,
      pullbackTensorLax f (A.obj n) (A.obj m) ≫
          (Modules.pullback f).map (A.mul n m) ≫ degreeMap (n + m) =
        tensorHom (degreeMap n) (degreeMap m) ≫ A'.mul n m) :
    GradedAlgebraComparison f A A' where
  degreeMap := degreeMap
  map_one := map_one
  map_mul := map_mul

/-- The unit and multiplication of `A` transport to those of `A'` along the degreewise
maps. -/
theorem spec (θ : GradedAlgebraComparison f A A') :
    (Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map A.unit ≫ θ.degreeMap 0 =
        A'.unit) ∧
      ∀ n m : ℤ,
        pullbackTensorLax f (A.obj n) (A.obj m) ≫
            (Modules.pullback f).map (A.mul n m) ≫ θ.degreeMap (n + m) =
          tensorHom (θ.degreeMap n) (θ.degreeMap m) ≫ A'.mul n m :=
  sorry

end GradedAlgebraComparison

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
