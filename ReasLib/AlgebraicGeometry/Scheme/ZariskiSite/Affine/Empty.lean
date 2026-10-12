/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Small

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineZariski

/-- The canonical empty affine open in the small affine Zariski site. -/
def empty (X : Scheme.{u}) : X.smallAffineZariskiSite where
  obj := ⊥
  property := isAffineOpen_bot X

/-- The underlying open of the canonical empty affine object. -/
theorem empty_obj (X : Scheme.{u}) :
    (empty X).obj = (⊥ : X.Opens) := sorry

end AlgebraicGeometry.Scheme.AffineZariski

end
