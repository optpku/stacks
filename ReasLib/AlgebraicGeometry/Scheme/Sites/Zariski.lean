module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig

/-!
# Zariski site infrastructure

Convenience import for the canonical big and small Zariski site presentations
and their cross-layer topos relation API. Applications should import the
narrow `Zariski.Big`, `Zariski.Small`, or `Zariski.SmallToBig` leaf when one
layer suffices.
-/
