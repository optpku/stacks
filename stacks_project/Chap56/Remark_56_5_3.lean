module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ProjectionFormula
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Remark 56.5.3 (0FZE): affine projection formula for quasi-coherent module sheaves. -/
@[stacks 0FZE] #check (AlgebraicGeometry.Scheme.Modules.affineProjectionFormula :
    ∀ {T S : Scheme.{u}} (h : T ⟶ S) [IsAffineHom h]
    (G : T.Modules) (H : S.Modules) [G.IsQuasicoherent] [H.IsQuasicoherent],
    IsIsomorphic (((Scheme.Modules.pushforward h).obj G) ⊗ H)
      ((Scheme.Modules.pushforward h).obj (G ⊗ (Scheme.Modules.pullback h).obj H)))

end AlgebraicGeometry.Scheme.Modules
