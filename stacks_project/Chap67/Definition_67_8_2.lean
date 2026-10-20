module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
import StacksCheckRecall

@[expose] public section

/- Definition 67.8.2: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
quasi-compact if for every quasi-compact algebraic space `Z` and morphism `Z ⟶ Y`, the
fibre product `Z ×_Y X` is a quasi-compact algebraic space. -/
@[stacks 03HE] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiCompact :
    ∀ {S : AlgebraicGeometry.Scheme}
      {X Y : AlgebraicGeometry.AlgebraicSpace S},
      (X ⟶ Y) → Prop)
