module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Horizontal composition of twisted derived base change -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

variable {S : Scheme.{u}}

variable {X'' X' X Y'' Y' Y : AlgebraicSpace S}
variable (g' : X'' ⟶ X') (g : X' ⟶ X)
variable (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
variable (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
variable (left : IsPullback g' f'' f' h') (right : IsPullback g f' f h)
variable (hTorRight : TorIndependentOver (Over.mk f) (Over.mk h))
variable (hTorLeft : TorIndependentOver (Over.mk f') (Over.mk h'))

/-- For horizontally adjacent cartesian squares of quasi-compact
quasi-separated algebraic spaces over a scheme, with the two indicated pairs Tor
independent, the canonical twisted base-change maps compose to the canonical map
for the outer rectangle, through the canonical derived-pullback composition maps. -/
theorem twistedMap_paste_horiz
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
    (E : DerivedQCoh Y) :
    pullbackCompMap g' g (a.obj E) ≫
        (twistedMap (g' ≫ g) f'' f (h' ≫ h) (left.paste_horiz right)
          a a'' fAdj f''Adj
          (torIndependentOver_horizontalComposition g' g f'' f' f h' h left right
            hTorRight hTorLeft)).app E =
      (pullback g').map
          ((twistedMap g f' f h right a a' fAdj f'Adj hTorRight).app E) ≫
        (twistedMap g' f'' f' h' left a' a'' f'Adj f''Adj hTorLeft).app
          ((pullback h).obj E) ≫
        a''.map (pullbackCompMap h' h E) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange
