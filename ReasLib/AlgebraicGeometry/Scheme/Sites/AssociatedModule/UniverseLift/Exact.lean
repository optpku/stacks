module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CoefficientComparison
public import ReasLib.CategoryTheory.Functor.Exactness.Composition

/-! # Exact universe lifting of module sheaves -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- Universe lifting of small-site module sheaves preserves finite limits and
finite colimits. -/
theorem smallModuleLift_exact (X : Scheme.{u}) (τ : StandardTopology) :
    exactFunctor _ _ (smallModuleLift X τ) := sorry

/-- Universe lifting of small-site module sheaves preserves addition of maps. -/
instance smallModuleLift_additive (X : Scheme.{u}) (τ : StandardTopology) :
    (smallModuleLift X τ).Additive where
  map_add {F G f g} := by
    ext U x
    rfl

/-- The universe lift of small-site module sheaves bundled as an exact functor. -/
def smallModuleLiftExact (X : Scheme.{u}) (τ : StandardTopology) :
    SheafOfModules.{u} (StandardSmall.structureSheaf τ X) ⥤ₑ
      RingedSite.ModuleCat.{u + 1} (smallCommRingedSite τ X) :=
  ⟨smallModuleLift X τ, smallModuleLift_exact X τ⟩

/-- Coefficient transport followed by universe lifting is an exact functor
from canonical étale module sheaves to the lifted commutative presentation. -/
def etaleModuleLiftExact (X : Scheme.{u}) :
    SheafOfModules.{u} (Etale.Small.structureSheaf X) ⥤ₑ
      RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale X) :=
  (ExactFunctor.of (etaleModulePresentation X).functor).comp
    (smallModuleLiftExact X .etale)

/-- The functor transporting canonical étale modules to the lifted
commutative coefficient presentation. -/
def etaleModuleLift (X : Scheme.{u}) :
    SheafOfModules.{u} (Etale.Small.structureSheaf X) ⥤
      RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale X) :=
  (etaleModuleLiftExact X).obj

end AlgebraicGeometry.Scheme.AssociatedModule
