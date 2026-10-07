module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.QuasiAffine
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 36.36.4: a quasi-affine morphism of schemes pulls the resolution property
back from a quasi-compact and quasi-separated target. In particular, this applies to
affine morphisms. -/
@[stacks 0F88] #check
  (AlgebraicGeometry.Scheme.hasResolutionProperty_of_quasiAffineHom :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y],
      HasResolutionProperty Y → QuasiAffineHom f → HasResolutionProperty X)

/- The affine special case. -/
#check
  (AlgebraicGeometry.Scheme.hasResolutionProperty_of_isAffineHom :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [CompactSpace Y]
      [QuasiSeparatedSpace Y], HasResolutionProperty Y → HasResolutionProperty X)

end AlgebraicGeometry.Scheme
