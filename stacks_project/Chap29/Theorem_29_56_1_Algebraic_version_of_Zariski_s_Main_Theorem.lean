module

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] [Scheme.Hom.FiniteType f]

/- Theorem 29.56.1 (Algebraic version of Zariski's Main Theorem): if
`f : Y ⟶ X` is affine and of finite type, then there is an open subscheme of the
normalization of `X` in `Y` over which `Y` is isomorphic, whose inverse image is exactly
the quasi-finite locus of `f`. -/
@[stacks 03GT] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization f :
    ∃ U' : f.normalization.Opens,
      IsIso (f.toNormalization ∣_ U') ∧
        ((f.toNormalization ⁻¹ᵁ U' : Y.Opens) : Set Y) =
          { y : Y | f.QuasiFiniteAt y })

end AlgebraicGeometry
