module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative.Homothety

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

/-- Two relative dualizing complexes for the same flat locally finitely presented morphism
and diagonal neighborhood admit a unique compatible isomorphism of their underlying complexes. -/
theorem existsUniqueIso
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ W.ι = pullback.diagonal f)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
    (K L : Scheme.RelativeDualizingComplex f W δ hδ H) :
    ∃! e : K.complex ≅ L.complex,
      K.map ≫ (RingedSpace.modulePullbackDerived
        (W.ι ≫ pullback.fst f f).toShHom).map e.hom = L.map := sorry

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
