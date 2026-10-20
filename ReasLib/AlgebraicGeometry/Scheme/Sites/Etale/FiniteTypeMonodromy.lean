module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteTypeMonodromy.AssociatedSheaf

/-!
# Finite-type étale module monodromy

On an irreducible geometrically unibranch scheme, finite-type locally constant
module sheaves are equivalent to finitely generated discrete representations
of the étale fundamental group over an arbitrary coefficient ring.
-/

public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch) (xbar : GeometricPoint X)

/-- Finite-type locally constant module sheaves on an irreducible geometrically
unibranch scheme are equivalent to finitely generated discrete representations
of its geometric fundamental group. -/
def finiteTypeLocallyConstantModule_equivalence_finitePi1Modules :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ≌
      (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory where
  functor := finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar
  inverse := FiniteTypeMonodromy.AssociatedSheaf.functor Λ xbar
  unitIso := FiniteTypeMonodromy.AssociatedSheaf.unitIso Λ xbar huni
  counitIso := FiniteTypeMonodromy.AssociatedSheaf.counitIso Λ xbar huni
  functor_unitIso_comp := FiniteTypeMonodromy.AssociatedSheaf.triangle Λ xbar huni

/-- The finite-type monodromy functor is an equivalence, as witnessed by its
associated-sheaf inverse and explicit natural comparison maps. -/
instance finiteTypeLocallyConstantModuleToFinitePi1Modules_isEquivalence :
    (finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar).IsEquivalence :=
  (finiteTypeLocallyConstantModule_equivalence_finitePi1Modules Λ huni xbar).isEquivalence_functor

end AlgebraicGeometry.Scheme
