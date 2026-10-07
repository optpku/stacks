module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard

/-!
# Associated modules on the standard scheme sites

This source bridge records the uniform associated-module constructions on the five
standard big sites and on the small Zariski and small étale sites of a scheme.
-/

universe u

#check (AlgebraicGeometry.SmallStandardTopology : Type)

#check
  (AlgebraicGeometry.Scheme.AssociatedModule.big :
    ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u})
      (F : S.Modules) [F.IsQuasicoherent],
      SheafOfModules (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureSheaf τ S))

#check
  (AlgebraicGeometry.Scheme.AssociatedModule.small :
    ∀ (σ : AlgebraicGeometry.SmallStandardTopology) (S : AlgebraicGeometry.Scheme.{u})
      (F : S.Modules) [F.IsQuasicoherent],
      SheafOfModules (AlgebraicGeometry.Scheme.AssociatedModule.smallStructureSheaf σ S))
