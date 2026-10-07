module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Quasicoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-coherence of associated module sheaves

Associated module sheaves are quasi-coherent because module sheaves on a ringed point are
quasi-coherent and pullback preserves quasi-coherence. This file owns the quasi-coherent codomain
lift and its colimit-preservation instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- Lemma 17.10.5 (3) (01BH): every associated module sheaf is quasi-coherent. -/
@[stacks 01BH "(3)"]
instance obj_isQuasicoherent (alpha : R →+* X.globalSectionsRing) (M : ModuleCat.{u} R) :
    (obj alpha M).IsQuasicoherent := sorry

/-- The associated-module functor with codomain restricted to quasi-coherent module sheaves. -/
@[stacks 01BH "quasi-coherent functor"]
noncomputable def qcFunctor (alpha : R →+* X.globalSectionsRing) :
    ModuleCat.{u} R ⥤ X.QCoh :=
  ObjectProperty.lift _ (functor alpha) (fun M ↦ obj_isQuasicoherent alpha M)

/-- Lemma 17.10.5 (4) (01BH): the quasi-coherent lift of the associated-module functor preserves
arbitrary colimits. -/
@[stacks 01BH "(4)"]
noncomputable instance qcFunctor_preservesColimits (alpha : R →+* X.globalSectionsRing) :
    PreservesColimits (qcFunctor alpha) := sorry

end AlgebraicGeometry.RingedSpace.Module.Associated
