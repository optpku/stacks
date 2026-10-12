/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra
public import ReasLib.Algebra.Homology.HomologicalComplex.Monoidal.Component
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
public import ReasLib.CategoryTheory.GradedObject.Monoid
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded algebra sheaves as monoid objects

A differential graded algebra is canonically a monoid object in the monoidal category of cochain
complexes.  This file assembles the unit and multiplication from their homogeneous components and
packages the construction functorially.  Relative tensor products can consequently use Mathlib's
generic bimodule API instead of a parallel sheaf-specific tensor-product interface.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedAlgebra

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

/-- Assemble the degree-zero unit of a differential graded algebra sheaf into a cochain map from
the tensor unit. -/
noncomputable def oneHom (A : DGA(𝒪)) :
    𝟙_ (CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪) ℤ) ⟶
      A.toComplex where
  f n :=
    (HomologicalComplex.tensorUnitIso
      (ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (up ℤ)).inv n ≫
      CategoryTheory.GradedObject.Monoidal.oneHom A.toComplex.X A.one n
  comm' := sorry

/-- Assemble homogeneous multiplication of a differential graded algebra sheaf into a morphism
of cochain complexes. -/
noncomputable def mulHom (A : DGA(𝒪)) :
    HomologicalComplex.tensorObj A.toComplex A.toComplex ⟶ A.toComplex where
  f n := HomologicalComplex.mapBifunctorDesc
    (K₁ := A.toComplex) (K₂ := A.toComplex)
    (F := curriedTensor (ringedSiteModuleCategory.{u, v, w, w} J 𝒪)) (c := up ℤ)
    fun p q h ↦ A.mul p q ≫ eqToHom (congrArg A.toComplex.X h)
  comm' := sorry

/-- A differential graded algebra sheaf as the canonical monoid object in cochain complexes. -/
@[stacks 0FRF "cochain-complex monoid bridge"]
noncomputable def toMon (A : DGA(𝒪)) :
    Mon (CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪) ℤ) where
  X := A.toComplex
  mon :=
    { one := oneHom A
      mul := mulHom A
      one_mul := sorry
      mul_one := sorry
      mul_assoc := sorry }

/-- A differential graded algebra map as a morphism of monoid objects in cochain complexes. -/
noncomputable def toMonMap {A B : DGA(𝒪)} (f : A ⟶ B) : A.toMon ⟶ B.toMon :=
  Mon.Hom.mk' f.hom sorry sorry

/-- The canonical functor from differential graded algebra sheaves to monoid objects in cochain
complexes. -/
@[stacks 0FRF "functorial cochain-complex monoid bridge"]
noncomputable def toMonFunctor :
    DGA(𝒪) ⥤ Mon (CochainComplex
      (ringedSiteModuleCategory.{u, v, w, w} J 𝒪) ℤ) where
  obj := toMon
  map := toMonMap
  map_id := sorry
  map_comp := sorry

/-- The underlying cochain complex of `A.toMon` is the original complex of `A`. -/
@[simp]
theorem toMon_X (A : DGA(𝒪)) : A.toMon.X = A.toComplex := sorry

/-- The unit of `A.toMon` is assembled from the degree-zero unit of `A`. -/
@[simp]
theorem toMon_one (A : DGA(𝒪)) : A.toMon.mon.one = oneHom A := sorry

/-- The multiplication of `A.toMon` is assembled from homogeneous multiplication of `A`. -/
@[simp]
theorem toMon_mul (A : DGA(𝒪)) : A.toMon.mon.mul = mulHom A := sorry

/-- The monoid-object bridge sends a differential graded algebra map to its underlying cochain
map. -/
@[simp]
theorem toMonMap_hom {A B : DGA(𝒪)} (f : A ⟶ B) :
    (toMonMap f).hom = f.hom := sorry

/-- Extracting the degree-zero component of the assembled unit recovers the original unit. -/
@[simp]
theorem oneHom_component (A : DGA(𝒪)) :
    HomologicalComplex.Monoidal.unitHomComponent (oneHom A) = A.one := sorry

/-- Extracting a homogeneous component of the assembled multiplication recovers the original
degreewise multiplication. -/
@[simp]
theorem mulHom_component (A : DGA(𝒪)) (n m : ℤ) :
    HomologicalComplex.Monoidal.tensorHomComponent (mulHom A) n m = A.mul n m := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedAlgebra

end
