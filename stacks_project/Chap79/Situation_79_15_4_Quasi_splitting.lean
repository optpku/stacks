module

import ReasLib.AlgebraicGeometry.GroupoidScheme.QuasiSplitting
import StacksCheckRecall

universe u

/- Situation 79.15.4 (Quasi-splitting): let `S` be a scheme, `(U, R, s, t, c)` a
groupoid scheme over `S`, and `u` a point of `U`. Assume `s` and `t` are
separated and locally of finite type, and `s` is quasi-finite at `e(u)`. -/
@[stacks 04RV] #check (AlgebraicGeometry.GroupoidScheme.IsQuasiSplittingSituation :
  {S : AlgebraicGeometry.Scheme.{u}} →
    (G : AlgebraicGeometry.GroupoidScheme S) → G.U.left → Prop)
