module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Restriction-of-scalars pairs

A pair `(a, b)` for morphisms `X ⟶ Z ⟶ B` of algebraic spaces over a scheme
`S`, consisting of a morphism `a : T ⟶ B` and a morphism
`b : T ×_{a,B} Z ⟶ X` over `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictScalars

/-- A pair `(a, b)` consisting of a morphism `a : T ⟶ B` over `S` and a
morphism `b : T ×_{a,B} Z ⟶ X` over `Z`. -/
structure Pair {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
    (T : AlgebraicSpace S) where
  /-- The morphism `a : T ⟶ B` over `S`. -/
  a : T ⟶ B
  /-- The morphism `b : T ×_{a,B} Z ⟶ X` from the fibre product `pullback a g`. -/
  b : pullback a g ⟶ X
  /-- The morphism `b` lies over `Z`, i.e. the triangle `b ≫ f = pullback.snd a g`
  commutes. -/
  overZ : b ≫ f = pullback.snd a g

namespace Pair

/-- Build a restriction-of-scalars pair from a morphism `a : T ⟶ B`, a morphism
`b : T ×_{a,B} Z ⟶ X`, and the over-`Z` triangle. -/
def of {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (a : T ⟶ B) (b : pullback a g ⟶ X) (h : b ≫ f = pullback.snd a g) :
    Pair f g T where
  a := a
  b := b
  overZ := h

/-- A restriction-of-scalars pair consists of the over-`Z` triangle together with
the pullback cone identity on `T ×_{a,B} Z`. -/
theorem spec {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (p : Pair f g T) :
    p.b ≫ f = pullback.snd p.a g ∧
      pullback.fst p.a g ≫ p.a = pullback.snd p.a g ≫ g := sorry

/-- The type of restriction-of-scalars pairs for a scheme `T` over `S`, recovered
as an algebraic space via `ofOver`. -/
abbrev over {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
    (T : Over S) :=
  Pair f g (ofOver T)

/-- Two restriction-of-scalars pairs are equal if their morphisms `a` and `b`
agree. -/
theorem ext {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    {p q : Pair f g T} (ha : p.a = q.a) (hb : HEq p.b q.b) : p = q := sorry

/-- The maps `pr₀ ≫ h` and `pr₁` out of `T' ×_B Z` agree over `B`, so they
induce `h × id_Z : T' ×_B Z ⟶ T ×_B Z`. -/
theorem fiberMap_condition {S : Scheme.{u}} {X Z B T T' : AlgebraicSpace S}
    {f : X ⟶ Z} {g : Z ⟶ B} (p : Pair f g T) (h : T' ⟶ T) :
    (pullback.fst (h ≫ p.a) g ≫ h) ≫ p.a = pullback.snd (h ≫ p.a) g ≫ g := sorry

/-- The comparison `h × id_Z : T' ×_B Z ⟶ T ×_B Z` induced by `h : T' ⟶ T`. -/
def fiberMap {S : Scheme.{u}} {X Z B T T' : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} (p : Pair f g T) (h : T' ⟶ T) :
    pullback (h ≫ p.a) g ⟶ pullback p.a g :=
  pullback.lift (pullback.fst (h ≫ p.a) g ≫ h) (pullback.snd (h ≫ p.a) g)
    (fiberMap_condition p h)

/-- The comparison `fiberMap p h` commutes with the first projections via `h`. -/
theorem fiberMap_fst {S : Scheme.{u}} {X Z B T T' : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} (p : Pair f g T) (h : T' ⟶ T) :
    fiberMap p h ≫ pullback.fst p.a g = pullback.fst (h ≫ p.a) g ≫ h := sorry

/-- The comparison `fiberMap p h` commutes with the second projections. -/
theorem fiberMap_snd {S : Scheme.{u}} {X Z B T T' : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} (p : Pair f g T) (h : T' ⟶ T) :
    fiberMap p h ≫ pullback.snd p.a g = pullback.snd (h ≫ p.a) g := sorry

/-- Base change of a pair along `h : T' ⟶ T` preserves the over-`Z` triangle. -/
theorem map_overZ {S : Scheme.{u}} {X Z B T T' : AlgebraicSpace S} {f : X ⟶ Z}
    {g : Z ⟶ B} (p : Pair f g T) (h : T' ⟶ T) :
    (fiberMap p h ≫ p.b) ≫ f = pullback.snd (h ≫ p.a) g := sorry

/-- Base change of a pair `(a, b)` along `h : T' ⟶ T`, sending `a` to `h ≫ a`
and `b` to the composite `(h × id_Z) ≫ b`. -/
def map {S : Scheme.{u}} {X Z B T T' : AlgebraicSpace S} {f : X ⟶ Z} {g : Z ⟶ B}
    (p : Pair f g T) (h : T' ⟶ T) : Pair f g T' where
  a := h ≫ p.a
  b := fiberMap p h ≫ p.b
  overZ := sorry

end Pair

end AlgebraicGeometry.AlgebraicSpace.RestrictScalars
