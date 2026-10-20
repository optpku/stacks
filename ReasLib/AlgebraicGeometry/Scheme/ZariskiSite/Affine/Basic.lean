/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Basic.Big
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Basic.Small

/-!
# Affine big and small Zariski site carriers

Convenience import for the affine-object restrictions of the big and small
Zariski sites. The big carrier reuses `Scheme.AffineOver`; the small carrier
uses affine opens with arbitrary inclusions. The separate leaves also expose
the ambient restricted topologies used to compare these carriers with finite
standard distinguished-open covers.
-/
