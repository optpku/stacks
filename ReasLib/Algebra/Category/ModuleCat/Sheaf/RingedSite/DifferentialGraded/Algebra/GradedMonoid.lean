module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Monoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying graded monoids of differential graded algebra sheaves

Forgetting the differential of a differential graded algebra retains a monoid object in the
monoidal category of integer-graded module sheaves.  This is the algebra owner used by relative
graded tensor products and graded flatness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
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

-- Local declaration justification (parser conflict): these lexical aliases shorten the ambient
-- module and graded categories without competing with the public `DGA(𝒪)` notation scope.
local notation "ModO" => moduleCategory (J := J) (𝒪 := 𝒪)
local notation "GrdO" => GradedObject ℤ ModO

/-- Assemble the degree-zero unit of a differential graded algebra as a morphism of graded
objects. -/
noncomputable def gradedOneHom (A : DGA(𝒪)) : 𝟙_ GrdO ⟶ A.toComplex.X :=
  CategoryTheory.GradedObject.Monoidal.oneHom A.toGradedObject A.one

/-- Assemble homogeneous multiplication of a differential graded algebra as a morphism of
graded objects. -/
noncomputable def gradedMulHom (A : DGA(𝒪)) :
    A.toGradedObject ⊗ A.toGradedObject ⟶ A.toGradedObject :=
  CategoryTheory.GradedObject.Monoidal.mulHom A.toGradedObject A.mul

/-- The underlying graded monoid of a differential graded algebra sheaf. -/
@[stacks 0FSA "underlying graded monoid of a differential graded algebra"]
noncomputable def toGradedMon (A : DGA(𝒪)) : Mon GrdO where
  X := A.toGradedObject
  mon :=
    { one := gradedOneHom A
      mul := gradedMulHom A
      one_mul := sorry
      mul_one := sorry
      mul_assoc := sorry }

/-- A differential graded algebra map as a morphism of underlying graded monoids. -/
noncomputable def toGradedMonMap {A B : DGA(𝒪)} (f : A ⟶ B) :
    A.toGradedMon ⟶ B.toGradedMon :=
  Mon.Hom.mk' f.hom.f sorry sorry

/-- Forgetting differentials gives a functor from differential graded algebras to graded monoid
objects. -/
@[stacks 0FSA "underlying graded monoid functor"]
noncomputable def toGradedMonFunctor : DGA(𝒪) ⥤ Mon GrdO where
  obj := toGradedMon
  map := toGradedMonMap
  map_id := sorry
  map_comp := sorry

/-- The carrier of the underlying graded monoid is the graded object of homogeneous pieces. -/
@[simp]
theorem toGradedMon_X (A : DGA(𝒪)) : A.toGradedMon.X = A.toComplex.X := sorry

/-- The unit of the underlying graded monoid is the assembled degree-zero unit. -/
@[simp]
theorem toGradedMon_one (A : DGA(𝒪)) :
    A.toGradedMon.mon.one = gradedOneHom A := sorry

/-- Multiplication of the underlying graded monoid is assembled from homogeneous products. -/
@[simp]
theorem toGradedMon_mul (A : DGA(𝒪)) :
    A.toGradedMon.mon.mul = gradedMulHom A := sorry

/-- The underlying map of a graded-monoid bridge is the degreewise algebra map. -/
@[simp]
theorem toGradedMonMap_hom {A B : DGA(𝒪)} (f : A ⟶ B) :
    (toGradedMonMap f).hom = f.hom.f := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedAlgebra

end
