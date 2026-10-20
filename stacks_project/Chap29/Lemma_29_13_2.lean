module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 29.13.2 (1): quasi-affine morphisms are separated. -/
@[stacks 01SL] #check
  (AlgebraicGeometry.QuasiAffineHom.isSeparated :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.QuasiAffineHom f → AlgebraicGeometry.IsSeparated f)

/- Lemma 29.13.2 (2): quasi-affine morphisms are quasi-compact. -/
@[stacks 01SL] #check
  (AlgebraicGeometry.QuasiAffineHom.quasiCompact :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.QuasiAffineHom f → AlgebraicGeometry.QuasiCompact f)
