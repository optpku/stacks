module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A pseudo-coherent derived module for a proper, flat, finitely presented morphism to
`Spec R` is perfect over `Spec R` if its derived pullback to `Spec (R ⧸ I)` is perfect and
`I ≤ Ring.jacobson R`. -/
theorem isPerfectOver_of_quotient_of_le_jacobson
    (R : CommRingCat.{u}) (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    {X : Scheme.{u}} (f : X ⟶ Spec R)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase (pullback.snd f (Spec.quotientMap I)).toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase (pullback.snd f (Spec.quotientMap I)).toShHom).restrict U.isOpenEmbedding))]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E)
    (hE₀ : RingedSpace.ModuleDerived.IsPerfectOver
      (pullback.snd f (Spec.quotientMap I)).toShHom
      ((RingedSpace.modulePullbackDerived
        (pullback.fst f (Spec.quotientMap I)).toShHom).obj E)) :
    RingedSpace.ModuleDerived.IsPerfectOver f.toShHom E := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
