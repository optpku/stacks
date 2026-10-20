module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.FullyFaithful
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.StandardSmall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski.Flat

/-!
# Associated-module functors with ambient module-sheaf codomain

The canonical associated-module functors naturally land in a quasi-coherent
full subcategory.  This module records their composites with the inclusion
into all module sheaves and the categorical properties of those composites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The big-site associated-module functor, viewed in the ambient category of
module sheaves. -/
noncomputable def bigModuleFunctor (S : Scheme.{u}) (τ : StandardTopology) :
    Scheme.QCoh S ⥤ SheafOfModules (bigStructureSheaf τ S) :=
  bigFunctor τ S ⋙ ObjectProperty.ι _

/-- On objects, the ambient big-site functor is the associated big-site module. -/
theorem bigModuleFunctor_obj (S : Scheme.{u}) (τ : StandardTopology)
    (F : Scheme.QCoh S) :
    (bigModuleFunctor S τ).obj F = big τ S F.obj := sorry

/-- On morphisms, the ambient big-site functor forgets only the
quasi-coherence witness. -/
theorem bigModuleFunctor_map (S : Scheme.{u}) (τ : StandardTopology)
    {F G : Scheme.QCoh S} (φ : F ⟶ G) :
    (bigModuleFunctor S τ).map φ = ((bigFunctor τ S).map φ).hom := sorry

/-- The small-standard-site associated-module functor, viewed in the ambient
category of module sheaves. -/
noncomputable def smallModuleFunctor (S : Scheme.{u}) (τ : StandardTopology) :
    Scheme.QCoh S ⥤ SheafOfModules (StandardSmall.structureSheaf τ S) :=
  StandardSmall.functor τ S ⋙ ObjectProperty.ι _

/-- On objects, the ambient small-standard-site functor has the canonical
pullback-sections presheaf. -/
theorem smallModuleFunctor_obj (S : Scheme.{u}) (τ : StandardTopology)
    (F : Scheme.QCoh S) :
    ((smallModuleFunctor S τ).obj F).val =
      Scheme.Modules.pullbackSectionsPresheaf
        (StandardTopology.Small.toOver τ S) F.obj := sorry

/-- On morphisms, the ambient small-standard-site functor applies the
pullback-sections functor. -/
theorem smallModuleFunctor_map (S : Scheme.{u}) (τ : StandardTopology)
    {F G : Scheme.QCoh S} (φ : F ⟶ G) :
    ((smallModuleFunctor S τ).map φ).val =
      (Scheme.Modules.pullbackSectionsFunctor
        (StandardTopology.Small.toOver τ S)).map φ.hom := sorry

/-- The ambient associated-module functor to every big standard site is fully
faithful. -/
theorem bigModuleFunctorFullyFaithful (S : Scheme.{u}) (τ : StandardTopology) :
    Nonempty (bigModuleFunctor S τ).FullyFaithful := sorry

/-- The ambient associated-module functor to every small standard site is fully
faithful. -/
theorem smallModuleFunctorFullyFaithful
    (S : Scheme.{u}) (τ : StandardTopology) :
    Nonempty (smallModuleFunctor S τ).FullyFaithful := sorry

/-- The ambient big-site associated-module functor preserves colimits of every
universe-compatible shape. -/
instance bigModuleFunctorPreservesColimits
    (S : Scheme.{u}) (τ : StandardTopology) (J : Type v) [Category.{w} J] :
    PreservesColimitsOfShape J (bigModuleFunctor S τ) := sorry

/-- The ambient small-standard-site associated-module functor preserves
colimits of every universe-compatible shape. -/
instance smallModuleFunctorPreservesColimits
    (S : Scheme.{u}) (τ : StandardTopology) (J : Type v) [Category.{w} J] :
    PreservesColimitsOfShape J (smallModuleFunctor S τ) := sorry

/-- The ambient associated-module functor to a big standard site is right exact. -/
theorem bigModuleFunctorRightExact (S : Scheme.{u}) (τ : StandardTopology) :
    rightExactFunctor (Scheme.QCoh S) (SheafOfModules (bigStructureSheaf τ S))
      (bigModuleFunctor S τ) := sorry

/-- The ambient associated-module functor to a small standard site is right exact. -/
theorem smallModuleFunctorRightExact (S : Scheme.{u}) (τ : StandardTopology) :
    rightExactFunctor (Scheme.QCoh S)
      (SheafOfModules (StandardSmall.structureSheaf τ S))
      (smallModuleFunctor S τ) := sorry

/-- The ambient associated-module functor to the small étale site is exact. -/
theorem smallEtaleModuleFunctorExact (S : Scheme.{u}) :
    exactFunctor (Scheme.QCoh S)
      (SheafOfModules (StandardSmall.structureSheaf .etale S))
      (smallModuleFunctor S .etale) := sorry

/-- The essential image of the ambient big-site associated-module functor is
closed under extensions. -/
instance bigEssImageClosedUnderExtensions
    (S : Scheme.{u}) (τ : StandardTopology) :
    (bigModuleFunctor S τ).essImage.IsClosedUnderExtensions := sorry

/-- The essential image of the ambient small-standard-site associated-module
functor is closed under extensions. -/
instance smallEssImageClosedUnderExtensions
    (S : Scheme.{u}) (τ : StandardTopology) :
    (smallModuleFunctor S τ).essImage.IsClosedUnderExtensions := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
