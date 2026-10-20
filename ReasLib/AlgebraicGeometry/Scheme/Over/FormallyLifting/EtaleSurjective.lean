module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Étale-on-top permanence for formally smooth, étale, and unramified transformations

Formal smoothness, étaleness, and unramifiedness of a transformation of functors
on schemes over a base are stable under precomposition with a representable
surjective étale transformation. Formal unramifiedness and étaleness also descend
along such a precomposition; formal smoothness yields an étale affine local lift
against an affine first-order thickening.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.Scheme.Over

namespace FormallySmooth

/-- An étale morphism of affines `π : U' ⟶ T'` together with a section
`z : G.obj (op U')` is an étale affine local lift of the solid square
`b.app (op T) x = H.map (op i) y` at the point `t` when the triangle
`U' ⟶ G ⟶ H` equals `U' ⟶ T' ⟶ H`, some fibre product `W = T ×_{T'} U'`
over `S` identifies the two maps to `G`, and `i.left t` lies in the image of
`π.left`. -/
def IsEtaleAffineLocalLift {S : Scheme.{u}} {G H : (Over S)ᵒᵖ ⥤ Type u}
    (b : G ⟶ H) {T T' U' : Over S} (i : T ⟶ T') (π : U' ⟶ T')
    (x : G.obj (op T)) (y : H.obj (op T')) (z : G.obj (op U'))
    (t : T.left) : Prop :=
  IsAffine U'.left ∧ Etale π.left ∧
    b.app (op U') z = H.map (op π) y ∧
      (∃ (W : Over S) (pT : W ⟶ T) (pU : W ⟶ U'),
          IsPullback pT.left pU.left i.left π.left ∧
            G.map (op pT) x = G.map (op pU) z) ∧
        i.left t ∈ Set.range π.left

/-- An étale affine local lift is equivalent to affinity and étaleness of `π`,
commutativity of both source squares, and the covering condition at `t`. -/
theorem isEtaleAffineLocalLift_iff {S : Scheme.{u}} {G H : (Over S)ᵒᵖ ⥤ Type u}
    (b : G ⟶ H) {T T' U' : Over S} (i : T ⟶ T') (π : U' ⟶ T')
    (x : G.obj (op T)) (y : H.obj (op T')) (z : G.obj (op U'))
    (t : T.left) :
    IsEtaleAffineLocalLift b i π x y z t ↔
      IsAffine U'.left ∧ Etale π.left ∧
        b.app (op U') z = H.map (op π) y ∧
          (∃ (W : Over S) (pT : W ⟶ T) (pU : W ⟶ U'),
              IsPullback pT.left pU.left i.left π.left ∧
                G.map (op pT) x = G.map (op pU) z) ∧
            i.left t ∈ Set.range π.left :=
  sorry

namespace IsEtaleAffineLocalLift

/-- An étale affine local lift may be assembled from affinity and étaleness of
`π`, commutativity of `U' ⟶ G ⟶ H` with `U' ⟶ T' ⟶ H`, a fibre-product
identification of the two maps to `G`, and the covering condition at `t`. -/
theorem of {S : Scheme.{u}} {G H : (Over S)ᵒᵖ ⥤ Type u} {b : G ⟶ H}
    {T T' U' : Over S} {i : T ⟶ T'} {π : U' ⟶ T'} {x : G.obj (op T)}
    {y : H.obj (op T')} {z : G.obj (op U')} {t : T.left}
    [IsAffine U'.left] [Etale π.left]
    (hH : b.app (op U') z = H.map (op π) y) {W : Over S}
    (pT : W ⟶ T) (pU : W ⟶ U')
    (hpb : IsPullback pT.left pU.left i.left π.left)
    (hG : G.map (op pT) x = G.map (op pU) z)
    (ht : i.left t ∈ Set.range π.left) :
    IsEtaleAffineLocalLift b i π x y z t :=
  sorry

/-- An étale affine local lift records affinity and étaleness of `π`, the two
source commutativities, and that `i.left t` lies in the image of `π.left`. -/
theorem spec {S : Scheme.{u}} {G H : (Over S)ᵒᵖ ⥤ Type u} {b : G ⟶ H}
    {T T' U' : Over S} {i : T ⟶ T'} {π : U' ⟶ T'} {x : G.obj (op T)}
    {y : H.obj (op T')} {z : G.obj (op U')} {t : T.left}
    (h : IsEtaleAffineLocalLift b i π x y z t) :
    IsAffine U'.left ∧ Etale π.left ∧
      b.app (op U') z = H.map (op π) y ∧
        (∃ (W : Over S) (pT : W ⟶ T) (pU : W ⟶ U'),
            IsPullback pT.left pU.left i.left π.left ∧
              G.map (op pT) x = G.map (op pU) z) ∧
          i.left t ∈ Set.range π.left :=
  sorry

end IsEtaleAffineLocalLift

/-- Formal smoothness of a transformation of functors is stable under
precomposition with a representable surjective étale transformation.
Here `a ≫ b` is the source composition `b ∘ a`. -/
theorem precomp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : (over (@Etale ⊓ @Surjective)).presheaf a) [FormallySmooth b] :
    FormallySmooth (a ≫ b) :=
  sorry

/-- Formal smoothness of functor transformations respects precomposition with
representable surjective étale transformations. -/
instance instRespectsLeft_etaleSurjective {S : Scheme.{u}} :
    RespectsLeft (@FormallySmooth S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u))
      (over (@Etale ⊓ @Surjective)).presheaf :=
  sorry

/-- If `a ≫ b` is formally smooth, then a solid square against an affine
first-order thickening lifts étale-locally on `T'` through an affine étale
`π : U' ⟶ T'` covering the image of any given point of `T`. -/
theorem exists_etaleAffineLocalLift {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (ha : (over (@Etale ⊓ @Surjective)).presheaf a) [FormallySmooth (a ≫ b)]
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left] (x : G.obj (op T)) (y : H.obj (op T'))
    (hx : b.app (op T) x = H.map (op i) y) (t : T.left) :
    ∃ (U' : Over S) (π : U' ⟶ T') (z : G.obj (op U')),
      IsEtaleAffineLocalLift b i π x y z t :=
  sorry

end FormallySmooth

namespace FormallyEtale

/-- Formal étaleness of a transformation of functors is stable under
precomposition with a representable surjective étale transformation.
Here `a ≫ b` is the source composition `b ∘ a`. -/
theorem precomp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : (over (@Etale ⊓ @Surjective)).presheaf a) [FormallyEtale b] :
    FormallyEtale (a ≫ b) :=
  sorry

/-- Formal étaleness of functor transformations respects precomposition with
representable surjective étale transformations. -/
instance instRespectsLeft_etaleSurjective {S : Scheme.{u}} :
    RespectsLeft (@FormallyEtale S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u))
      (over (@Etale ⊓ @Surjective)).presheaf :=
  sorry

/-- If `a ≫ b` is formally étale and `a` is representable, surjective, and
étale, then `b` is formally étale. Here `a ≫ b` is the source composition
`b ∘ a`. -/
theorem of_precomp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : (over (@Etale ⊓ @Surjective)).presheaf a) [FormallyEtale (a ≫ b)] :
    FormallyEtale b :=
  sorry

/-- Formal étaleness of functor transformations is cancellable on the right
against a representable surjective étale precomposition. -/
instance instHasOfPrecompProperty_etaleSurjective {S : Scheme.{u}} :
    HasOfPrecompProperty
      (@FormallyEtale S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u))
      (over (@Etale ⊓ @Surjective)).presheaf :=
  sorry

end FormallyEtale

namespace FormallyUnramified

/-- Formal unramifiedness of a transformation of functors is stable under
precomposition with a representable surjective étale transformation.
Here `a ≫ b` is the source composition `b ∘ a`. -/
theorem precomp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : (over (@Etale ⊓ @Surjective)).presheaf a) [FormallyUnramified b] :
    FormallyUnramified (a ≫ b) :=
  sorry

/-- Formal unramifiedness of functor transformations respects precomposition
with representable surjective étale transformations. -/
instance instRespectsLeft_etaleSurjective {S : Scheme.{u}} :
    RespectsLeft
      (@FormallyUnramified S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u))
      (over (@Etale ⊓ @Surjective)).presheaf :=
  sorry

/-- If `a ≫ b` is formally unramified and `a` is representable, surjective, and
étale, then `b` is formally unramified. Here `a ≫ b` is the source composition
`b ∘ a`. -/
theorem of_precomp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : (over (@Etale ⊓ @Surjective)).presheaf a)
    [FormallyUnramified (a ≫ b)] :
    FormallyUnramified b :=
  sorry

/-- Formal unramifiedness of functor transformations is cancellable on the
right against a representable surjective étale precomposition. -/
instance instHasOfPrecompProperty_etaleSurjective {S : Scheme.{u}} :
    HasOfPrecompProperty
      (@FormallyUnramified S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u))
      (over (@Etale ⊓ @Surjective)).presheaf :=
  sorry

end FormallyUnramified

end AlgebraicGeometry.Scheme.Over
