/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism

universe u

open CategoryTheory

namespace AlgebraicGeometry.GroupoidScheme.Hom

/- Situation 40.11.1 (1): an identity-on-objects morphism of groupoid schemes commutes with
the source maps. The field hypothesis in the Stacks setup is redundant for this statement. -/
@[stacks 04Q5] #check
  (AlgebraicGeometry.GroupoidScheme.Hom.IsIdentityOnObjects.source :
    ∀ {S : Scheme.{u}} {G H : GroupoidScheme S} {f : Hom G H}
      {hU : G.U = H.U}, f.IsIdentityOnObjects hU →
        f.arrow ≫ H.s = G.s ≫ eqToHom hU)

/- Situation 40.11.1 (2): an identity-on-objects morphism of groupoid schemes commutes with
the target maps. The field hypothesis in the Stacks setup is redundant for this statement. -/
@[stacks 04Q5] #check
  (AlgebraicGeometry.GroupoidScheme.Hom.IsIdentityOnObjects.target :
    ∀ {S : Scheme.{u}} {G H : GroupoidScheme S} {f : Hom G H}
      {hU : G.U = H.U}, f.IsIdentityOnObjects hU →
        f.arrow ≫ H.t = G.t ≫ eqToHom hU)

/- Situation 40.11.1 (3): an identity-on-objects morphism of groupoid schemes commutes with
groupoid composition. The field hypothesis in the Stacks setup is redundant for this statement. -/
@[stacks 04Q5] #check
  (AlgebraicGeometry.GroupoidScheme.Hom.IsIdentityOnObjects.map_c :
    ∀ {S : Scheme.{u}} {G H : GroupoidScheme S} {f : Hom G H}
      {hU : G.U = H.U}, f.IsIdentityOnObjects hU →
        G.c ≫ f.arrow = f.composableMap ≫ H.c)

end AlgebraicGeometry.GroupoidScheme.Hom
