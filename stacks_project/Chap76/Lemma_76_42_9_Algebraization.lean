module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Algebraization.Thickening

/-! Compatibility check for uniform stagewise kernel-and-cokernel annihilation. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X} [IsQuasiCoherent I],
    IdealSubobject X → {F G : CoherentFormalModules X I} → (F ⟶ G) → Prop)
