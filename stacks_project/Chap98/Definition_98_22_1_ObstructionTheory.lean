module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

#check (AlgebraicGeometry.GroupoidsOver.ObstructionTriple : GroupoidsOver S → Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.ObstructionTheory : GroupoidsOver S → Type (u + 1))

#check (AlgebraicGeometry.GroupoidsOver.ObstructionTriple.Hom.ofModuleHom :
  ∀ (ξ : ObjectOverSpec X) {M N : ModuleCat.{u} ξ.carrier} (f : M ⟶ N),
    ObstructionTriple.Hom (ObstructionTriple.of ξ M) (ObstructionTriple.of ξ N))

#check (AlgebraicGeometry.GroupoidsOver.ObstructionTheory.obstruction_eq_zero_iff_nonempty_objectLift :
  ∀ (𝒪 : ObstructionTheory X) (σ : DeformationSituation X),
    𝒪.obstruction σ = 0 ↔ Nonempty (DeformationSituation.ObjectLift σ))
