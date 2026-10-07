module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Ample
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.43.16: a projective morphism to a scheme admitting an ample invertible module is
H-projective. -/
@[stacks 087S] #check
  (AlgebraicGeometry.Projective.toHProjective_of_hasAmpleInvertibleModule :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}, Projective f →
      Scheme.Modules.HasAmpleInvertibleModule S → HProjective f)

#check
  (AlgebraicGeometry.QuasiProjective.toHQuasiProjective_of_hasAmpleInvertibleModule :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}, QuasiProjective f →
      Scheme.Modules.HasAmpleInvertibleModule S → HQuasiProjective f)
