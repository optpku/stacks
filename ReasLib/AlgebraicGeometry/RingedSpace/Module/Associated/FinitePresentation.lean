module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentations and associated module sheaves

Associated module sheaves preserve finite presentation.  Since the associated-module functor
preserves filtered colimits, it also carries filtered presentations by finitely presented modules
to filtered presentations by finitely presented module sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- Associated sheaves of finitely presented modules are finitely presented. -/
@[stacks 01BR "finite presentation"]
instance obj_isFinitePresentation
    (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    (obj alpha M).IsFinitePresentation := sorry

/-- Mapping a filtered presentation by finitely presented modules through the associated-module
functor gives a filtered presentation by finitely presented module sheaves. -/
@[stacks 01BR "filtered-colimit transport"]
theorem ind_obj_of_ind
    (alpha : R →+* X.globalSectionsRing) {M : ModuleCat.{u} R}
    (hM : (ModuleCat.isFinitePresentation.{u, u} R).ind.{u} M) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ind.{u} (obj alpha M) := sorry

/-- Lemma 17.11.6 (01BR): every associated module sheaf is a filtered colimit of finitely
presented module sheaves. -/
@[stacks 01BR]
theorem ind_obj (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ind.{u} (obj alpha M) := sorry

end AlgebraicGeometry.RingedSpace.Module.Associated
