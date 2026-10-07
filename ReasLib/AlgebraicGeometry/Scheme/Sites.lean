module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.All
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.All
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski

/-!
# Sites of schemes

This umbrella collects the reusable site constructions on schemes. The topology-independent
affine-slice and presentation owners are exported alongside the Zariski, etale, fppf, smooth,
syntomic, and proper-hypercovering specializations.

Downstream files should continue to import a focused leaf when they use only one topology or
one functoriality layer; this module is the discoverable broad entry point for scheme sites.
-/
