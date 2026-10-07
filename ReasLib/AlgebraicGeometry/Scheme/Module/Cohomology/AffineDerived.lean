module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.DerivedBaseChange

/-!
# Derivability of affine-base module functors

Associated modules and global sections over an affine base have their canonical unbounded
derived functors.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Associated-module formation over an affine base has its total left derived functor. -/
instance affineBaseModuleAssociatedFunctor_hasLeftDerived
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) :
    AffineBaseModuleDerivedAdjunction.HasLeftDerived A p := sorry

/-- Global sections over an affine base have their total right derived functor. -/
instance affineBaseModuleGlobalSectionsFunctor_hasRightDerived
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) :
    AffineBaseModuleDerivedAdjunction.HasRightDerived A p := sorry

end AlgebraicGeometry.Scheme.Modules
