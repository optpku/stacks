/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineTopology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 96.24.2 (1): the associated affine Zariski site
`X.affineZariskiTopology` is the structure of site on `X.Affine` inherited
from `(Aff/S)_Zar`. -/
@[stacks 0H0A] #check (AlgebraicGeometry.GroupoidsOver.affineZariskiTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    GrothendieckTopology (AlgebraicGeometry.GroupoidsOver.Affine X))

/- Definition 96.24.2 (2): the associated affine étale site
`X.affineEtaleTopology` is the structure of site on `X.Affine` inherited from
`(Aff/S)_étale`. -/
@[stacks 0H0A] #check (AlgebraicGeometry.GroupoidsOver.affineEtaleTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    GrothendieckTopology (AlgebraicGeometry.GroupoidsOver.Affine X))

/- Definition 96.24.2 (3): the associated affine smooth site
`X.affineSmoothTopology` is the structure of site on `X.Affine` inherited from
`(Aff/S)_smooth`. -/
@[stacks 0H0A] #check (AlgebraicGeometry.GroupoidsOver.affineSmoothTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    GrothendieckTopology (AlgebraicGeometry.GroupoidsOver.Affine X))

/- Definition 96.24.2 (4): the associated affine syntomic site
`X.affineSyntomicTopology` is the structure of site on `X.Affine` inherited
from `(Aff/S)_syntomic`. -/
@[stacks 0H0A] #check (AlgebraicGeometry.GroupoidsOver.affineSyntomicTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    GrothendieckTopology (AlgebraicGeometry.GroupoidsOver.Affine X))

/- Definition 96.24.2 (5): the associated affine fppf site
`X.affineFppfTopology` is the structure of site on `X.Affine` inherited from
`(Aff/S)_fppf`. -/
@[stacks 0H0A] #check (AlgebraicGeometry.GroupoidsOver.affineFppfTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    GrothendieckTopology (AlgebraicGeometry.GroupoidsOver.Affine X))
