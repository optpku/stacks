module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Associated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Topology
public import ReasLib.CategoryTheory.InverseSystem.Sequential

/-!
# Associated modules and sequential inverse limits

This file constructs the canonical comparison from the associated module of a sequential inverse
limit to the quasicoherent coreflection of the inverse limit of the associated modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.Module.Associated

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.DerivedQCoh.Associated

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The adjunct of the degree-zero image of the canonical map from the associated module of an
inverse limit to the inverse limit of the associated modules. -/
noncomputable def limitComparison (f : X ⟶ Spec (CommRingCat.of R))
    [Scheme.Hom.FinitePresentation f] (M : SequentialInverseSystem (ModuleCat.{u} R)) :
    single f (limit M) ⟶
      (@Functor.rightAdjoint _ _ _ _ (Scheme.ModuleDerived.Quasicoherent.inclusion X)
        (@DerivedQCoh.inclusionIsLeftAdjoint X
          (Scheme.Hom.compactSpace_of_finitePresentation f)
          (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).obj
        ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
          (limit (M ⋙ functor (Scheme.Hom.globalSectionsMap f)))) :=
  (@Adjunction.ofIsLeftAdjoint _ _ _ _ (Scheme.ModuleDerived.Quasicoherent.inclusion X)
    (@DerivedQCoh.inclusionIsLeftAdjoint X
      (Scheme.Hom.compactSpace_of_finitePresentation f)
      (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).homEquiv
      (single f (limit M))
      ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
        (limit (M ⋙ functor (Scheme.Hom.globalSectionsMap f))))
      ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).map
        (limit.post M (functor (Scheme.Hom.globalSectionsMap f))))

/-- Under the inclusion–coreflector adjunction, `limitComparison f M` corresponds to the
degree-zero image of the canonical map from the associated module of the limit. -/
theorem limitComparison_adjunct (f : X ⟶ Spec (CommRingCat.of R))
    [Scheme.Hom.FinitePresentation f] (M : SequentialInverseSystem (ModuleCat.{u} R)) :
    ((@Adjunction.ofIsLeftAdjoint _ _ _ _ (Scheme.ModuleDerived.Quasicoherent.inclusion X)
      (@DerivedQCoh.inclusionIsLeftAdjoint X
        (Scheme.Hom.compactSpace_of_finitePresentation f)
        (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).homEquiv
        (single f (limit M))
        ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
          (limit (M ⋙ functor (Scheme.Hom.globalSectionsMap f))))).symm
        (limitComparison f M) =
      (DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).map
        (limit.post M (functor (Scheme.Hom.globalSectionsMap f))) := sorry

/-- For a proper, flat, finitely presented morphism to an affine scheme and a sequential inverse
system of modules with epimorphic transitions, the associated-module limit comparison is an
isomorphism. -/
theorem limitComparison_isIso (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [IsProper f]
    [Scheme.Hom.FinitePresentation f] (M : SequentialInverseSystem (ModuleCat.{u} R))
    [∀ n : ℕ, Epi (SequentialInverseSystem.transitionMap M (Nat.le_succ n))] :
    IsIso (limitComparison f M) := sorry

end Scheme.DerivedQCoh.Associated
end AlgebraicGeometry
