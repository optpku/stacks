module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteTypeMonodromy
import StacksCheckRecall

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.65.2: finite-type locally constant sheaves of `Λ`-modules on the small
étale site of an irreducible geometrically unibranch scheme `X` are equivalent to
finite `Λ`-modules with a continuous `π₁(X, x̄)`-action, for an arbitrary ring `Λ`. -/
@[stacks 0GIY]
#check (AlgebraicGeometry.Scheme.finiteTypeLocallyConstantModule_equivalence_finitePi1Modules :
  ∀ {X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch) (xbar : GeometricPoint X),
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ≌
      (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)
