/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Extension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Remark 111.36.8 (1): if `j : U ⟶ X` is a quasi-compact immersion, then any
quasi-coherent sheaf on `U` is the pullback of a quasi-coherent sheaf on `X`.
The preceding affine exercise is easier and should not use these general facts. -/
@[stacks 029V] #check
  (AlgebraicGeometry.Scheme.Modules.exists_quasiCoherentExtension_of_isImmersion :
    ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsImmersion j] [QuasiCompact j]
      (G : U.Modules) [G.IsQuasicoherent],
      ∃ H : X.Modules, H.IsQuasicoherent ∧ Nonempty ((pullback j).obj H ≅ G))

/- Remark 111.36.8 (2): if `X` is a Noetherian scheme and `U ⊆ X` is open, then any
coherent sheaf on `U` is the restriction of a coherent sheaf on `X`. -/
@[stacks 029V] #check
  (AlgebraicGeometry.Scheme.Modules.exists_coherentExtension :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens)
      (G : (U : Scheme).Modules) [G.IsCoherent],
      ∃ H : X.Modules, H.IsCoherent ∧ Nonempty (H.restrict U.ι ≅ G))

end AlgebraicGeometry.Scheme.Modules
