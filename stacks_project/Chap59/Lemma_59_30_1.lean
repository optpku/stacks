/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.EnoughPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Scheme

universe u

/- Lemma 59.30.1 (1): the small affine Zariski site has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_smallAffineZariski :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (smallAffineZariskiTopology S))

/- Lemma 59.30.1 (2): the small Zariski site has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_smallZariski :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (smallZariskiTopology S))

/- Lemma 59.30.1 (3): the small affine étale site has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_smallAffineEtale :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1} (AffineEtale.topology S))

/- Lemma 59.30.1 (4): the small étale site has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_smallEtale :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u} (smallEtaleTopology S))

/- Lemma 59.30.1 (5): the big Zariski site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_bigZariski :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1} (zariskiTopology.over S))

/- Lemma 59.30.1 (6): the affine-over Zariski site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_affineZariski :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (affineOverTopology S (zariskiTopology.over S)))

/- Lemma 59.30.1 (7): the big étale site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_bigEtale :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (S.overGrothendieckTopology (@Etale)))

/- Lemma 59.30.1 (8): the affine-over étale site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_affineEtale :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (affineOverTopology S (S.overGrothendieckTopology (@Etale))))

/- Lemma 59.30.1 (9): the big smooth site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_bigSmooth :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (S.overGrothendieckTopology (@Smooth)))

/- Lemma 59.30.1 (10): the affine-over smooth site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_affineSmooth :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (affineOverTopology S (S.overGrothendieckTopology (@Smooth))))

/- Lemma 59.30.1 (11): the big syntomic site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_bigSyntomic :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (S.overGrothendieckTopology (@Syntomic)))

/- Lemma 59.30.1 (12): the affine-over syntomic site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_affineSyntomic :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (affineOverTopology S (S.overGrothendieckTopology (@Syntomic))))

/- Lemma 59.30.1 (13): the big fppf site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_bigFppf :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1} (fppfTopology.over S))

/- Lemma 59.30.1 (14): the affine-over fppf site over `S` has enough points. -/
@[stacks 06VX] #check
  (AlgebraicGeometry.Scheme.hasEnoughPoints_affineFppf :
    ∀ (S : Scheme.{u}),
      GrothendieckTopology.HasEnoughPoints.{u + 1}
        (affineOverTopology S (fppfTopology.over S)))
