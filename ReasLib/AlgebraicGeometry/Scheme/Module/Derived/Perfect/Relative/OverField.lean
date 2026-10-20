module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

/-!
# Relative perfectness over a field

This file characterizes relative perfectness for derived modules on schemes of finite
presentation over a field.
-/

open CategoryTheory DerivedCategory.TStructure

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.SchemeOverField

open RingedSpace RingedSpace.ModuleDerived

/-- A derived module on a scheme of finite presentation over a field is perfect relative to
the field if and only if it is cohomologically bounded and pseudo-coherent. -/
theorem isPerfectOver_iff_bounded_and_pseudoCoherent {k : Type u} [Field k]
    (X : SchemeOverField k) [Scheme.Hom.FinitePresentation X.hom]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase X.hom.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase X.hom.toShHom).restrict U.isOpenEmbedding))]
    (E : ModuleDerived X.left.toRingedSpace) :
    IsPerfectOver X.hom.toShHom E ↔
      t.bounded E ∧ RingedSpace.ModuleDerived.IsPseudoCoherent E := sorry

/-- A derived module on a scheme of finite presentation over a field is perfect relative to
the field if and only if it is cohomologically bounded and has coherent cohomology in every
degree. -/
theorem isPerfectOver_iff_bounded_and_coherentCohomology {k : Type u} [Field k]
    (X : SchemeOverField k) [Scheme.Hom.FinitePresentation X.hom]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase X.hom.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase X.hom.toShHom).restrict U.isOpenEmbedding))]
    (E : ModuleDerived X.left.toRingedSpace) :
    IsPerfectOver X.hom.toShHom E ↔
      t.bounded E ∧
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (Scheme.ringCatSheaf X.left)) E := sorry

end AlgebraicGeometry.SchemeOverField
