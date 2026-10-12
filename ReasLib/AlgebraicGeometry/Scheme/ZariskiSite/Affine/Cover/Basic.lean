/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.StandardZariskiCover.AffineFamily
public import ReasLib.AlgebraicGeometry.Scheme.StandardZariskiCover.AffineOpen
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Basic

/-!
# Basic standard-cover data for affine Zariski sites

Convenience import for the geometry data required by the big and small affine
Zariski cover pretopologies. The finite cover data is owned by
`PrimeSpectrum.StandardOpenCoverOf`; `StandardZariskiCover/AffineFamily` and
`StandardZariskiCover/AffineOpen` provide its affine-slice and ambient-open
views.
-/
