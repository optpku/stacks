module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.DualizingModule
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualizingModule.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingModule

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The contravariant functor sending a coherent module `F` to the maps from its degree-`d`
cohomology to the fixed `A`-module `W`. -/
noncomputable abbrev cohomologyDualFunctor {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) (W : ModuleCat.{u} A) :
    (RingedSpace.Coh X.toRingedSpace)ᵒᵖ ⥤ Type u :=
  ((SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
      cohomologyFunctor f d).op ⋙ yoneda.obj W

/-- Evaluation of `cohomologyDualFunctor f d W` is
`F ↦ (cohomology f F.unop.obj d ⟶ W)`. -/
theorem cohomologyDualFunctor_obj {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ) (W : ModuleCat.{u} A)
    (F : (RingedSpace.Coh X.toRingedSpace)ᵒᵖ) :
    (cohomologyDualFunctor f d W).obj F =
      (cohomology f F.unop.obj d ⟶ W) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.ExceptionalInverseImage

/-- Under the proper local-Noetherian dimension hypotheses, the dualizing module represents
the functor taking a coherent module to maps from its top closed-fibre cohomology into the
base dualizing module. -/
theorem representsCohomologyDual
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωA : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωA.IsNormalizedDualizingComplex HA)
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (fShriek : Scheme.ExceptionalInverseImage f)
    (d n : ℕ)
    (h_closed : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint A)) = d)
    (h_total : topologicalKrullDim X = n)
    (h_add : topologicalKrullDim X = (d : WithBot ℕ∞) + ringKrullDim A)
    (ωX : X.Modules)
    (hωX : RingedSpace.ModuleDerived.IsDualizingModule
      (fShriek.functor.obj ωS) HX (-(n : ℤ)) ωX) :
    Nonempty ((Scheme.Hom.cohomologyDualFunctor f d
      (DerivedCategory.IsNormalizedDualizingComplex.dualizingModule HA ωA hωA)).RepresentableBy
        hωX.toCoh) := sorry

end AlgebraicGeometry.Scheme.ExceptionalInverseImage
