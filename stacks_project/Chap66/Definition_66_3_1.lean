module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.3.1 (1): an algebraic space `X` over a scheme `S` is separated if
`extendBaseTerminal X` is separated, equivalently if `diag (extendBaseTerminal X)` is a
closed immersion. -/
@[stacks 03BS] #check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelySeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

/- Definition 66.3.1 (2): an algebraic space `X` over a scheme `S` is locally separated if
`extendBaseTerminal X` is locally separated, equivalently if `diag (extendBaseTerminal X)` is
an immersion. -/
@[stacks 03BS] #check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyLocallySeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

/- Definition 66.3.1 (3): an algebraic space `X` over a scheme `S` is quasi-separated if
`extendBaseTerminal X` is quasi-separated, equivalently if `diag (extendBaseTerminal X)` is
quasi-compact. -/
@[stacks 03BS] #check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)

/- Definition 66.3.1 (4): an algebraic space `X` over a scheme `S` is Zariski locally
quasi-separated if `extendBaseTerminal X` admits a Zariski covering by quasi-separated open
subspaces. -/
@[stacks 03BS] #check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyZariskiLocallyQuasiSeparated :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
