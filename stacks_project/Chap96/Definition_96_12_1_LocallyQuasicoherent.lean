module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LocallyQuasicoherent

@[expose] public section

universe u

#check (AlgebraicGeometry.GroupoidsOver.IsLocallyQuasicoherent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S},
    PresheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj → Prop)
