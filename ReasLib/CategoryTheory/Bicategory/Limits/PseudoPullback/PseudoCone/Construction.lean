/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Diagram
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

/-!
# Walking-cospan pseudocone constructions

This neutral bridge constructs and deconstructs the walking-cospan presentation of a readable
`PseudoPullbackCone`. It contains only explicit cone data and the private coherence needed to
assemble a strong transformation. Field readouts and the bilimit predicate are provided by the
`Computations` and `Bilimit` leaves respectively.

The split follows the Stacks 003O/003Q distinction: a 2-commutative square is concrete data
(`PseudoPullbackCone`), while finality is a separate universal-property layer.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

namespace Implementation

/- Implementation boundary: walking-cospan constructors are used only to assemble the generic
cone. Public users consume the apex, projection, and generator simp facades in `Computations`. -/

/-- The three components used internally to assemble the generic pseudocone represented by a
readable pseudopullback square. -/
private def coneApp (S : PseudoPullbackCone f g) :
    ∀ a : LocallyDiscrete Limits.WalkingCospan, S.pt ⟶ (cospan f g).obj a
  | ⟨none⟩ => S.fst ≫ f
  | ⟨some Limits.WalkingPair.left⟩ => S.fst
  | ⟨some Limits.WalkingPair.right⟩ => S.snd

/-- The identity and generator naturality isomorphisms, indexed before the walking cospan is
wrapped as a locally discrete bicategory. -/
private def coneNaturalityOfHom (S : PseudoPullbackCone f g) :
    ∀ {a b : Limits.WalkingCospan} (h : a ⟶ b),
      𝟙 S.pt ≫ coneApp S (LocallyDiscrete.mk b) ≅
        coneApp S (LocallyDiscrete.mk a) ≫ (cospan f g).map (Quiver.Hom.toLoc h)
  | _, _, .id _ => λ_ _ ≪≫ (ρ_ _).symm
  | _, _, .term Limits.WalkingPair.left => λ_ _
  | _, _, .term Limits.WalkingPair.right => λ_ _ ≪≫ S.iso

/-- The naturality isomorphisms used internally to assemble the generic pseudocone. -/
private def coneNaturality (S : PseudoPullbackCone f g)
    {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b) :
    𝟙 S.pt ≫ coneApp S b ≅ coneApp S a ≫ (cospan f g).map h :=
  coneNaturalityOfHom S h.as

/-- Naturality in `2`-morphisms for the strong transformation represented by `S`; the
walking cospan is locally discrete. -/
private theorem coneNaturalityNaturality (S : PseudoPullbackCone f g) :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} {h k : a ⟶ b} (η : h ⟶ k),
      (Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) S.pt).map₂ η ▷
          coneApp S b ≫ (coneNaturality S k).hom =
        (coneNaturality S h).hom ≫
          coneApp S a ◁ (cospan f g).map₂ η := sorry
/- Proof strategy: use local discreteness to identify `h` and `k` and eliminate `η`. After
unfolding `coneNaturality` and both `map₂` actions, the equality is naturality of the unitors,
with the right generator additionally whiskering `S.iso`. -/

/-- Identity coherence for the strong transformation represented by `S`. -/
private theorem coneNaturalityId (S : PseudoPullbackCone f g) :
    ∀ a : LocallyDiscrete Limits.WalkingCospan,
      (coneNaturality S (𝟙 a)).hom ≫
        coneApp S a ◁ ((cospan f g).mapId a).hom =
        ((Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) S.pt).mapId a).hom ▷
          coneApp S a ≫
          (λ_ (coneApp S a)).hom ≫ (ρ_ (coneApp S a)).inv := sorry
/- Proof strategy: split `a` into the centre, left, and right vertices; unfold
`coneNaturality` and the two `mapId` isomorphisms, then normalize with bicategory unitor
coherence. -/

/-- Composition coherence for the strong transformation represented by `S`. -/
private theorem coneNaturalityComp (S : PseudoPullbackCone f g) :
    ∀ {a b c : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b) (k : b ⟶ c),
      (coneNaturality S (h ≫ k)).hom ≫
        coneApp S a ◁ ((cospan f g).mapComp h k).hom =
        ((Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) S.pt).mapComp h k).hom ▷
          coneApp S c ≫
          (α_ ((Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) S.pt).map h)
            ((Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) S.pt).map k)
            (coneApp S c)).hom ≫
          (Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) S.pt).map h ◁
            (coneNaturality S k).hom ≫
          (α_ ((Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) S.pt).map h)
            (coneApp S b) ((cospan f g).map k)).inv ≫
          (coneNaturality S h).hom ▷ (cospan f g).map k ≫
          (α_ (coneApp S a) ((cospan f g).map h) ((cospan f g).map k)).hom := sorry
/- Proof strategy: case-split `h` and `k` through `LocallyDiscrete` and `WalkingCospan`.
Unfold `coneNaturality`, `(cospan f g).mapComp`, and `Pseudofunctor.const`, then use the
bicategory triangle and pentagon coherence laws and naturality of `S.iso`. -/

end Implementation

/-- The generic walking-cospan pseudocone represented by a readable pseudopullback square.
This is the semantic bridge from the four-field source-facing presentation to `PseudoCone`. -/
def toPseudoCone (S : PseudoPullbackCone f g) : PseudoCone (cospan f g) :=
  PseudoCone.mk S.pt
    { app a := Implementation.coneApp S a
      naturality h := Implementation.coneNaturality S h
      naturality_naturality := Implementation.coneNaturalityNaturality S
      naturality_id := Implementation.coneNaturalityId S
      naturality_comp := Implementation.coneNaturalityComp S }

/-- Forget a generic walking-cospan pseudocone to its readable square presentation. The
comparison cell is obtained by passing through the cone component at the central vertex. -/
def ofPseudoCone (s : PseudoCone (cospan f g)) : PseudoPullbackCone f g where
  pt := s.pt
  fst := s.π.app (LocallyDiscrete.mk Limits.WalkingCospan.left)
  snd := s.π.app (LocallyDiscrete.mk Limits.WalkingCospan.right)
  iso :=
    (s.π.naturality (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)).symm ≪≫
      s.π.naturality (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)

/- Data audit (mathlib 4.32): `toPseudoCone` and `ofPseudoCone` construct/read all apex,
projection, and comparison data explicitly. Their deferred fields are only the Prop-valued
naturality and coherence laws required by the generic strong transformation. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
