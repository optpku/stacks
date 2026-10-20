module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints

/-!
# Injectivity from weakly associated points

A morphism of quasi-coherent modules on an algebraic space is a monomorphism
when its geometric étale stalk maps are injective at weakly associated points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- A morphism of quasi-coherent modules on an algebraic space is a monomorphism
if at every point either its étale stalk maps at all geometric points above that
point are injective or the point is not weakly associated to the source. -/
@[stacks 0CUR]
theorem mono_of_stalkwise_injective_or_not_mem_weakAss
    (φ : F ⟶ G)
    (hφ : ∀ x : Points X,
      (∀ xbar : GeometricPoint X,
          xbar.liesOver x → Function.Injective (stalkModuleCatMap xbar φ)) ∨
        x ∉ F.weakAss) :
    Mono φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
