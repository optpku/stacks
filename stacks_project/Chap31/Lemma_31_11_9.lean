module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Exact

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 31.11.9: Let `X` be an integral scheme. If the outer terms of a short exact
sequence of quasicoherent `𝒪_X`-modules are torsion free, then its middle term is torsion free. -/
@[stacks 0AXX] #check
  (AlgebraicGeometry.Scheme.Modules.IsTorsionFree.middle_of_shortExact :
    ∀ {X : Scheme.{u}} [IsIntegral X] {S : ShortComplex X.Modules}
      [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
      (_ : S.ShortExact)
      [AlgebraicGeometry.Scheme.Modules.IsTorsionFree S.X₁]
      [AlgebraicGeometry.Scheme.Modules.IsTorsionFree S.X₃],
      AlgebraicGeometry.Scheme.Modules.IsTorsionFree S.X₂)
