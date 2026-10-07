module

public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver

/-!
# Base change of relatively flat modules on algebraic spaces

In a cartesian square of algebraic spaces, relative flatness of a quasi-coherent module at a
point is preserved by pullback, and is reflected when the base morphism is flat at the image
point. In particular, global relative flatness is preserved by pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 67.31.3 (1): in a cartesian square of algebraic spaces, relative flatness of a
quasi-coherent module at a point is preserved by pullback. -/
@[stacks 05VW]
theorem flatOverAt_pullback_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent] (x' : Points X')
    (hflat : flatOverAt F f (Points.map g' x')) :
    flatOverAt ((pullback g').obj F) f' x' :=
  sorry

/-- Lemma 67.31.3 (2): in a cartesian square of algebraic spaces, relative flatness of a
quasi-coherent module at a point is reflected when the base morphism is flat at the image of
that point. -/
@[stacks 05VW]
theorem flatOverAt_of_isPullback_of_flatAt_base {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent] (x' : Points X')
    (hbase : FlatAt g (Points.map f' x'))
    (hflat : flatOverAt ((pullback g').obj F) f' x') :
    flatOverAt F f (Points.map g' x') :=
  sorry

/-- Lemma 67.31.3 (3): in a cartesian square of algebraic spaces, global relative flatness of a
quasi-coherent module is preserved by pullback. -/
@[stacks 05VW]
theorem flatOver_pullback_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent]
    (hflat : flatOver F f) :
    flatOver ((pullback g').obj F) f' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
