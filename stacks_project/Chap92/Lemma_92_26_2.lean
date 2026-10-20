module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.EtaleLocalization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 92.26.2. For a commutative square of algebraic spaces over a scheme with
étale vertical maps, the restriction of `L_{X/Y}` to the small étale site of `U`
is canonically identified with `L_{U/V}` in `D(𝒪_U)`. -/
@[stacks 08VE] #check (AlgebraicGeometry.AlgebraicSpace.Cotangent.etaleRestrictIso :
  ∀ {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (q : V ⟶ Y) (g : U ⟶ V) (f : X ⟶ Y)
    [Etale p] [Etale q] (sq : CommSq g p q f),
    Cotangent.pullbackCotangent p f ≅ Cotangent.cotangent g)
