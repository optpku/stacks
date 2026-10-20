module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Linearity
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
variable [Abelian (RingedSpace.Coh X.toRingedSpace)]
variable [Abelian (RingedSpace.Coh Y.toRingedSpace)]
variable [HasDerivedCategory.{u} (RingedSpace.Coh X.toRingedSpace)]
variable [HasDerivedCategory.{u} (RingedSpace.Coh Y.toRingedSpace)]

/-- The scalar structure on the bounded derived category of coherent modules induced by a
structure morphism to the spectrum of a field. The coherent scalar action is transported to
the abelian preadditive structure, then extended to the derived category and its bounded
full subcategory. -/
@[implicit_reducible]
noncomputable def baseLinearBoundedCoh (f : X ⟶ Spec (CommRingCat.of k)) :
    Linear k (DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace)) :=
  @Linear.fullSubcategory _ _ _ k _
    (@DerivedCategory.instLinear k _ (RingedSpace.Coh X.toRingedSpace) _ _
      (Eq.mp (congrArg
        (fun p : Preadditive (RingedSpace.Coh X.toRingedSpace) ↦
          @Linear k _ (RingedSpace.Coh X.toRingedSpace) _ p)
        (@Subsingleton.elim _
          (@CategoryTheory.subsingleton_preadditive_of_hasBinaryBiproducts
            (RingedSpace.Coh X.toRingedSpace) _
            (@Preadditive.preadditiveHasZeroMorphisms _ _ Abelian.toPreadditive)
            (@Abelian.hasBinaryBiproducts _ _ inferInstance)) _ _)) (baseLinearCoh f)) _)
    t.bounded

/-- A functor between bounded derived categories of coherent modules is linear over two
structure morphisms when it is additive and preserves their induced scalar actions. -/
class LinearOverBoundedCoh
    (F : DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
      DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace)) : Prop
    extends F.Additive,
      @Functor.Linear k _
        (DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace))
        (DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace)) _ _ _ _
        (baseLinearBoundedCoh x) (baseLinearBoundedCoh y) F

/-- Relative linearity on bounded coherent derived categories is equivalent to additivity
and linearity for the two base-induced scalar structures. -/
theorem linearOverBoundedCoh_iff
    (F : DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
      DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace)) :
    LinearOverBoundedCoh x y F ↔
      F.Additive ∧
        @Functor.Linear k _
          (DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace))
          (DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace)) _ _ _ _
          (baseLinearBoundedCoh x) (baseLinearBoundedCoh y) F := sorry

end AlgebraicGeometry.Scheme
