module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.DeformationSituation

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

#check (AlgebraicGeometry.Scheme.Hom.MapsIntoAffineOpen :
  ∀ {T S : Scheme.{u}}, (T ⟶ S) → Prop)

#check (AlgebraicGeometry.GroupoidsOver.ObjectOverSpec : GroupoidsOver S → Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.DeformationSituation : GroupoidsOver S → Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.DeformationSituation.kernelModule :
  (σ : DeformationSituation X) → ModuleCat.{u} σ.carrier)

#check (AlgebraicGeometry.GroupoidsOver.DeformationSituation.Hom.kernelMap :
  ∀ {σ τ : DeformationSituation X} (f : DeformationSituation.Hom σ τ),
    σ.kernelModule ⟶ (ModuleCat.restrictScalars f.toRingHom).obj τ.kernelModule)
