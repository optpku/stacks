/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Contraction.UnderlyingSet
public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Contraction.FreeResolution

/-!
# Contractions of polynomial resolutions

This compatibility facade exposes the independent underlying-set and free-resolution
contractions. Downstream files may import either semantic leaf directly.
-/

@[expose] public section
