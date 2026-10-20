module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.13.8: a morphism over a base from a quasi-affine morphism to a
quasi-separated morphism is quasi-affine. -/
@[stacks 054G] #check
  (AlgebraicGeometry.QuasiAffineHom.of_over_quasiSeparated :
    ∀ {X Y S : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S} {g : X ⟶ Y},
      g ≫ y = x → QuasiAffineHom x → QuasiSeparated y → QuasiAffineHom g)

/- In particular, every morphism from a quasi-affine scheme to a
quasi-separated scheme is quasi-affine. -/
#check
  (AlgebraicGeometry.Scheme.IsQuasiAffine.quasiAffineHom_of_quasiSeparated :
    ∀ {X Y : Scheme.{u}} (g : X ⟶ Y) (hX : X.IsQuasiAffine) [QuasiSeparatedSpace Y],
      QuasiAffineHom g)
