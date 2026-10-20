module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt.Near

/-!
# Pseudo-coherent morphisms of algebraic spaces

A morphism of algebraic spaces is pseudo-coherent when every étale scheme square
over it has pseudo-coherent top arrow. Pointwise pseudo-coherence is
pseudo-coherence after restriction to an open subspace neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is pseudo-coherent if
every commutative square with étale vertical arrows from schemes has
pseudo-coherent top arrow. -/
class PseudoCoherent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- Every étale scheme square over `f` has pseudo-coherent top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.PseudoCoherent h.left

/-- A morphism of algebraic spaces is pseudo-coherent if and only if every
commutative square with étale vertical arrows from schemes has pseudo-coherent
top arrow. -/
theorem pseudoCoherent_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    PseudoCoherent f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.PseudoCoherent h.left :=
  sorry

namespace PseudoCoherent

/-- An étale scheme square over a pseudo-coherent morphism of algebraic spaces
has pseudo-coherent top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [PseudoCoherent f] {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.PseudoCoherent h.left :=
  sorry

/-- The identity morphism of an algebraic space is pseudo-coherent. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : PseudoCoherent (𝟙 X) :=
  sorry

/-- A representable morphism of algebraic spaces with the relative
pseudo-coherent property is pseudo-coherent. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.PseudoCoherent :
          MorphismProperty Scheme.{u})).presheaf f) :
    PseudoCoherent f :=
  sorry

end PseudoCoherent

/-- A morphism of algebraic spaces is pseudo-coherent if and only if it has the
étale-local lift of scheme-level pseudo-coherence. -/
theorem pseudoCoherent_iff_etaleLocal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    PseudoCoherent f ↔
      etaleLocal
        (@AlgebraicGeometry.PseudoCoherent : MorphismProperty Scheme.{u}) f :=
  sorry

/-- A morphism `f : X ⟶ Y` of algebraic spaces is pseudo-coherent at a point `x`
of `X` if it is pseudo-coherent after restriction to some open subspace
neighbourhood of `x`. -/
def PseudoCoherentAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ PseudoCoherent (i ≫ f)

/-- Pseudo-coherence at a point is the existence of an open subspace
neighbourhood on which the morphism is pseudo-coherent. -/
theorem pseudoCoherentAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    PseudoCoherentAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          PseudoCoherent (i ≫ f) :=
  sorry

namespace PseudoCoherentAt

/-- An open immersion `i : X' ⟶ X` whose composite `i ≫ f` is pseudo-coherent
witnesses that `f` is pseudo-coherent at every point of the image of `|X'|`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [PseudoCoherent (i ≫ f)] : PseudoCoherentAt f x :=
  sorry

end PseudoCoherentAt

/-- A pseudo-coherent morphism of algebraic spaces is pseudo-coherent at every
point of its source. -/
theorem pseudoCoherentAt_of_pseudoCoherent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [PseudoCoherent f] (x : Points X) :
    PseudoCoherentAt f x :=
  sorry

/-- Pseudo-coherence at a point is equivalent to the neighbourhood étale-local
lift of scheme-level pseudo-coherence at that point. -/
theorem pseudoCoherentAt_iff_etaleLocalNear {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    PseudoCoherentAt f x ↔
      etaleLocalNear
        (@AlgebraicGeometry.PseudoCoherent : MorphismProperty Scheme.{u}) f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
