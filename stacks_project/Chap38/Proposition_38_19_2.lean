module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.LocallyProjective.Affine

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Proposition 38.19.2: for an affine finitely presented morphism and a finitely presented
module flat over the base, local projectivity of its pushforward is equivalent to relative
purity. -/
@[stacks 05MD]
#check (AlgebraicGeometry.Scheme.Modules.pushforward_isLocallyProjective_iff_isPureOver :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] [IsAffineHom f]
      (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F f),
    ((Scheme.Modules.pushforward f).obj F).IsLocallyProjective ↔ F.IsPureOver f)

/- For a finitely presented algebra and a finitely presented module flat over its base, the
module is projective over the base exactly when its associated sheaf is relatively pure. -/
#check AlgebraicGeometry.Scheme.Modules.module_projective_iff_tilde_isPureOver

end AlgebraicGeometry.Scheme.Modules
