/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.ImprovementAlong

import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.15.5 (1): a coherent module on a Noetherian scheme with local dualizing
complexes admits a unique depth improvement along `T' ⊆ T`, up to a unique compatible target
isomorphism. -/
@[stacks 0EI4] #check (AlgebraicGeometry.Scheme.Modules.IsDepthImprovementAlong.existsUniqueIso :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    (T' T : Set X)
    (hT' : StableUnderSpecialization T')
    (hT : StableUnderSpecialization T)
    (hTT' : T' ⊆ T)
    (h_immediate : ∀ ⦃x x' : X⦄,
      IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
    (hdual : LocallyHasDualizingComplex X)
    (F : X.Modules) [F.IsCoherent],
    ∃ (G : X.Modules) (hG : G.IsCoherent) (φ : F ⟶ G),
      IsDepthImprovementAlong T' T φ ∧
        ∀ (H : X.Modules) (hH : H.IsCoherent) (ψ : F ⟶ H),
          IsDepthImprovementAlong T' T ψ →
            ∃! e : G ≅ H, φ ≫ e.hom = ψ)

/- Lemma 51.15.5 (2): Cohen--Macaulay pullback preserves the depth improvement property
over the inverse-image pair `f⁻¹' T' ⊆ f⁻¹' T`. -/
@[stacks 0EI4] #check (AlgebraicGeometry.Scheme.Modules.IsDepthImprovementAlong.pullback_of_cohenMacaulay :
  ∀ {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (T' T : Set X)
    (hT' : StableUnderSpecialization T')
    (hT : StableUnderSpecialization T)
    (hTT' : T' ⊆ T)
    (h_immediate : ∀ ⦃x x' : X⦄,
      IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (φ : F ⟶ G) (hφ : IsDepthImprovementAlong T' T φ)
    (f : Y ⟶ X) [AlgebraicGeometry.CohenMacaulay f],
    IsDepthImprovementAlong (f.base ⁻¹' T') (f.base ⁻¹' T) ((pullback f).map φ))

end AlgebraicGeometry.Scheme.Modules

-- Declarations for this item will be appended below by the statement pipeline.
