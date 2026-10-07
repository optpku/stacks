module

import StacksCheckRecall
import stacks_project.Chap82.Remark_82_22_2_TrivialGysin

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (k : ℤ)
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)
variable (htriv : isUnitObject ((Modules.pullback (zeroSchemeι L s)).obj L))

/- Remark 82.22.2: Let `S`, `B`, `X`, `L`, `s` and `i : D ⟶ X` be as in
Definition 82.22.1, and assume that the pullback of `L` to `D = Z(s)` is
isomorphic to `𝒪_D`. Then there is a canonical additive map
`i* : Z_{k+1}(X) ⟶ Z_k(D)` on cycles, determined by `i*[W] = 0` whenever
`W ⊆ D`. -/
@[stacks 0ER2] #check (Hom.trivialGysin f δ k L s htriv :
  f.cycleGroup δ (k + 1) →+ (zeroSchemeι L s ≫ f).cycleGroup δ k)

end AlgebraicGeometry.AlgebraicSpace
