module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Locality
import StacksCheckRecall

/-!
# Characterizations of étaleness for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.39.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is étale;
`f` is étale at every point of `X`; every base change of `f` along a
morphism from a scheme is étale; every base change of `f` along a morphism
from an affine scheme is étale; there is a surjective étale morphism from
a scheme to `Y` along which the base change of `f` is étale; there is a
surjective étale morphism `φ` from a scheme to `X` with `φ ≫ f` étale;
every étale scheme square over `f` has étale top arrow; some étale scheme
square over `f` with surjective vertical source arrow has étale top arrow;
and there are Zariski coverings of `Y` and of the inverse images in `X` on
which the pieces of `f` are étale. -/
@[stacks 03XT] #check (AlgebraicGeometry.AlgebraicSpace.etale_tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ Etale f
      , ∀ x : Points X, EtaleAt f x
      , Etale.baseChangeOnSchemes f
      , Etale.baseChangeOnAffineSchemes f
      , Etale.existsOnTarget f
      , Etale.existsOnSource f
      , etaleLocal (fun _ _ h ↦ AlgebraicGeometry.Etale h) f
      , Etale.existsSquare f
      , Etale.existsZariskiCover.{u, v} f ])

end AlgebraicGeometry.AlgebraicSpace
