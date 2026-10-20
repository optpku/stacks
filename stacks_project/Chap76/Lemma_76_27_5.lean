module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Noetherian
public import stacks_project.Chap66.Lemma_66_24_4
public import stacks_project.Chap76.Lemma_76_27_3_Gorenstein

/-!
# Flat morphisms from Gorenstein algebraic spaces

A flat morphism of locally Noetherian algebraic spaces with Gorenstein source is
Gorenstein, and the étale local ring of the target at the image of every
geometric point of the source is a Gorenstein local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Gorenstein

/-- Lemma 76.27.5 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
locally Noetherian algebraic spaces over `S`. If `X` is Gorenstein, then `f` is
Gorenstein. -/
@[stacks 0E17]
instance of_flat_of_source {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [IsGorenstein X] :
    Gorenstein f :=
  sorry

end Gorenstein

namespace IsGorenstein

/-- Lemma 76.27.5 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
locally Noetherian algebraic spaces over `S`. If `X` is Gorenstein, then
`𝒪_{Y, f(x̄)}`, that is `etaleLocalRing Y (xbar.map f)`, is a Gorenstein local
ring for every geometric point `x̄` of `X`. -/
@[stacks 0E17]
theorem instTargetEtaleLocalRingOfFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    [IsGorenstein X] (xbar : GeometricPoint X) :
    -- Local instance justification (proof-local temporary data): IsGorensteinLocalRing requires the explicit canonical locality proof as a class argument here; keep it local without registering a global companion instance.
    letI := etaleLocalRing.instIsLocalRing (xbar.map f)
    IsGorensteinLocalRing (etaleLocalRing Y (xbar.map f)) :=
  sorry

end IsGorenstein

end AlgebraicGeometry.AlgebraicSpace
