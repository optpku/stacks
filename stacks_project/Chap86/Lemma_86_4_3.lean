/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange.HorizontalComposition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

noncomputable section

universe u

/- Lemma 86.4.3: for horizontally adjacent cartesian squares of quasi-compact
quasi-separated algebraic spaces over a scheme, with the two indicated pairs Tor
independent, the canonical twisted base-change maps compose to the canonical map
for the outer rectangle, through the canonical derived-pullback composition maps. -/
@[stacks 0E5F] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange.twistedMap_paste_horiz :
    ∀ {S : Scheme.{u}}
    {X'' X' X Y'' Y' Y : AlgebraicSpace S}
    (g' : X'' ⟶ X') (g : X' ⟶ X)
    (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
    (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
    (left : IsPullback g' f'' f' h') (right : IsPullback g f' f h)
    (hTorRight : TorIndependentOver (Over.mk f) (Over.mk h))
    (hTorLeft : TorIndependentOver (Over.mk f') (Over.mk h'))

    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact X'] [IsAbsolutelyQuasiSeparated X']
    [IsQuasiCompact X''] [IsAbsolutelyQuasiSeparated X'']
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [IsQuasiCompact Y'] [IsAbsolutelyQuasiSeparated Y']
    [IsQuasiCompact Y''] [IsAbsolutelyQuasiSeparated Y'']
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (a'' : DerivedQCoh Y'' ⥤ DerivedQCoh X'')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (f''Adj : pushforwardCohomologyIn f'' ⊣ a'')
    (E : DerivedQCoh Y),
    pullbackCompMap g' g (a.obj E) ≫
        (twistedMap (g' ≫ g) f'' f (h' ≫ h) (left.paste_horiz right)
          a a'' fAdj f''Adj
          (torIndependentOver_horizontalComposition g' g f'' f' f h' h left right
            hTorRight hTorLeft)).app E =
      (pullback g').map
          ((twistedMap g f' f h right a a' fAdj f'Adj hTorRight).app E) ≫
        (twistedMap g' f'' f' h' left a' a'' f'Adj f''Adj hTorLeft).app
          ((pullback h).obj E) ≫
        a''.map (pullbackCompMap h' h E))
