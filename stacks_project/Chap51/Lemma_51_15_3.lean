/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.Improvement
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.15.3 (1): on a Noetherian universally catenary scheme with `(S₁)` formal
fibers, a coherent module has a coherent depth improvement along any closed subset,
unique up to a unique target isomorphism compatible with the source map. -/
@[stacks 0DX5]
#check (AlgebraicGeometry.Scheme.Modules.IsDepthImprovement.existsUniqueIso :
    ∀ {X : Scheme.{u}}
    [IsNoetherian X] [UniversallyCatenary X]
    (Z : TopologicalSpace.Closeds X) (F : X.Modules) [F.IsCoherent]
    (h_formal : ∀ x : X,
      (FieldAlgebraProperty.serreConditionS 1).HoldsOnFormalFibers
        (X.presheaf.stalk x)),
    ∃ (G : X.Modules) (hG : G.IsCoherent) (φ : F ⟶ G),
      IsDepthImprovement Z φ ∧
        ∀ (H : X.Modules) (hH : H.IsCoherent) (ψ : F ⟶ H),
          IsDepthImprovement Z ψ →
            ∃! e : G ≅ H, φ ≫ e.hom = ψ)

/- Lemma 51.15.3 (2): Cohen–Macaulay pullback preserves a depth improvement over the
inverse-image closed subset. -/
@[stacks 0DX5]
#check (AlgebraicGeometry.Scheme.Modules.IsDepthImprovement.pullback_of_cohenMacaulay :
    ∀ {X Y : Scheme.{u}}
    [IsNoetherian X] [UniversallyCatenary X] [IsNoetherian Y]
    (Z : TopologicalSpace.Closeds X) (F G : X.Modules)
    [F.IsCoherent] [G.IsCoherent] (φ : F ⟶ G)
    (hφ : IsDepthImprovement Z φ)
    (h_formal : ∀ x : X,
      (FieldAlgebraProperty.serreConditionS 1).HoldsOnFormalFibers
        (X.presheaf.stalk x))
    (f : Y ⟶ X) [AlgebraicGeometry.CohenMacaulay f],
    IsDepthImprovement (Z.preimage f.continuous) ((pullback f).map φ))

end AlgebraicGeometry.Scheme.Modules
