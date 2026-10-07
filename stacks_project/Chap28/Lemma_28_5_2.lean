module

public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

variable (X : Scheme.{u})

#check (@AlgebraicGeometry.IsLocallyNoetherian.mk X :
  (∀ U : X.affineOpens, IsNoetherianRing Γ(X, U)) → IsLocallyNoetherian X)

#check (@AlgebraicGeometry.IsLocallyNoetherian.component_noetherian X :
  IsLocallyNoetherian X → ∀ U : X.affineOpens, IsNoetherianRing Γ(X, U))

variable {ι : Type v} {S : ι → X.affineOpens}
  (hS : (⨆ i, S i : X.Opens) = ⊤)

/- Lemma 28.5.2: A scheme is locally Noetherian exactly when the section rings on the members of
an affine open covering family are Noetherian; equivalently this can be checked on an affine open
cover or on an open cover, and every open subscheme is locally Noetherian. -/
@[stacks 01OW] #check
  (AlgebraicGeometry.isLocallyNoetherian_iff_of_iSup_eq_top (X := X) hS :
    IsLocallyNoetherian X ↔ ∀ i, IsNoetherianRing Γ(X, S i))

#check (AlgebraicGeometry.Scheme.affineOpenCover X : X.AffineOpenCover)

variable (𝒰 : X.OpenCover)

#check (AlgebraicGeometry.isLocallyNoetherian_iff_openCover 𝒰 :
  IsLocallyNoetherian X ↔ ∀ i : 𝒰.I₀, IsLocallyNoetherian (𝒰.X i))

variable [IsLocallyNoetherian X] (U : X.Opens)

#check (AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion U.ι :
  IsLocallyNoetherian U.toScheme)

end AlgebraicGeometry
