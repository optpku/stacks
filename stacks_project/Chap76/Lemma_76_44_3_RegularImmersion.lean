/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import stacks_project.Chap65.Lemma_65_12_4_Immersion

/-!
# Regular immersions of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is a Koszul-regular,
`H₁`-regular, or quasi-regular immersion when it is an immersion and every
represented pullback along an étale morphism from a scheme to the target is
the corresponding regular immersion of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `i : Z ⟶ X` of algebraic spaces over `S` is a Koszul-regular
immersion if it is an immersion and every represented pullback along an étale
morphism from a scheme to `X` is a Koszul-regular immersion of schemes. -/
class IsKoszulRegularImmersion {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) : Prop extends IsImmersion i where
  /-- After any étale morphism from a scheme to the target, a represented
  pullback of `i` is a Koszul-regular immersion of schemes. -/
  of_etale_target {V W : Over S} (b : yoneda.obj V ⟶ X.functorOfPoints)
      (fst : yoneda.obj W ⟶ Z.functorOfPoints) (snd : W ⟶ V) :
    (over (@AlgebraicGeometry.Etale)).presheaf b →
      IsPullback fst (yoneda.map snd) i b →
        AlgebraicGeometry.IsKoszulRegularImmersion snd.left

/-- A morphism `i : Z ⟶ X` of algebraic spaces over `S` is an `H₁`-regular
immersion if it is an immersion and every represented pullback along an étale
morphism from a scheme to `X` is an `H₁`-regular immersion of schemes. -/
class IsH1RegularImmersion {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) : Prop extends IsImmersion i where
  /-- After any étale morphism from a scheme to the target, a represented
  pullback of `i` is an `H₁`-regular immersion of schemes. -/
  of_etale_target {V W : Over S} (b : yoneda.obj V ⟶ X.functorOfPoints)
      (fst : yoneda.obj W ⟶ Z.functorOfPoints) (snd : W ⟶ V) :
    (over (@AlgebraicGeometry.Etale)).presheaf b →
      IsPullback fst (yoneda.map snd) i b →
        AlgebraicGeometry.IsH1RegularImmersion snd.left

/-- A morphism `i : Z ⟶ X` of algebraic spaces over `S` is a quasi-regular
immersion if it is an immersion and every represented pullback along an étale
morphism from a scheme to `X` is a quasi-regular immersion of schemes. -/
class IsQuasiRegularImmersion {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) : Prop extends IsImmersion i where
  /-- After any étale morphism from a scheme to the target, a represented
  pullback of `i` is a quasi-regular immersion of schemes. -/
  of_etale_target {V W : Over S} (b : yoneda.obj V ⟶ X.functorOfPoints)
      (fst : yoneda.obj W ⟶ Z.functorOfPoints) (snd : W ⟶ V) :
    (over (@AlgebraicGeometry.Etale)).presheaf b →
      IsPullback fst (yoneda.map snd) i b →
        AlgebraicGeometry.IsQuasiRegularImmersion snd.left

/-- A morphism of algebraic spaces is a Koszul-regular immersion iff it is an
immersion and every étale-on-target represented pullback is a Koszul-regular
immersion of schemes. -/
theorem isKoszulRegularImmersion_iff {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) :
    IsKoszulRegularImmersion i ↔
      IsImmersion i ∧
        ∀ {V W : Over S} (b : yoneda.obj V ⟶ X.functorOfPoints)
          (fst : yoneda.obj W ⟶ Z.functorOfPoints) (snd : W ⟶ V),
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            IsPullback fst (yoneda.map snd) i b →
              AlgebraicGeometry.IsKoszulRegularImmersion snd.left :=
  sorry

/-- A morphism of algebraic spaces is an `H₁`-regular immersion iff it is an
immersion and every étale-on-target represented pullback is an `H₁`-regular
immersion of schemes. -/
theorem isH1RegularImmersion_iff {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) :
    IsH1RegularImmersion i ↔
      IsImmersion i ∧
        ∀ {V W : Over S} (b : yoneda.obj V ⟶ X.functorOfPoints)
          (fst : yoneda.obj W ⟶ Z.functorOfPoints) (snd : W ⟶ V),
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            IsPullback fst (yoneda.map snd) i b →
              AlgebraicGeometry.IsH1RegularImmersion snd.left :=
  sorry

/-- A morphism of algebraic spaces is a quasi-regular immersion iff it is an
immersion and every étale-on-target represented pullback is a quasi-regular
immersion of schemes. -/
theorem isQuasiRegularImmersion_iff {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) :
    IsQuasiRegularImmersion i ↔
      IsImmersion i ∧
        ∀ {V W : Over S} (b : yoneda.obj V ⟶ X.functorOfPoints)
          (fst : yoneda.obj W ⟶ Z.functorOfPoints) (snd : W ⟶ V),
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            IsPullback fst (yoneda.map snd) i b →
              AlgebraicGeometry.IsQuasiRegularImmersion snd.left :=
  sorry

/-- A Koszul-regular immersion of algebraic spaces is an immersion whose
étale-on-target represented pullbacks are Koszul-regular immersions of
schemes. -/
theorem IsKoszulRegularImmersion.spec {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsKoszulRegularImmersion i] :
    IsImmersion i ∧
      ∀ {V W : Over S} (b : yoneda.obj V ⟶ X.functorOfPoints)
        (fst : yoneda.obj W ⟶ Z.functorOfPoints) (snd : W ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf b →
          IsPullback fst (yoneda.map snd) i b →
            AlgebraicGeometry.IsKoszulRegularImmersion snd.left :=
  sorry

/-- An `H₁`-regular immersion of algebraic spaces is an immersion whose
étale-on-target represented pullbacks are `H₁`-regular immersions of
schemes. -/
theorem IsH1RegularImmersion.spec {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsH1RegularImmersion i] :
    IsImmersion i ∧
      ∀ {V W : Over S} (b : yoneda.obj V ⟶ X.functorOfPoints)
        (fst : yoneda.obj W ⟶ Z.functorOfPoints) (snd : W ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf b →
          IsPullback fst (yoneda.map snd) i b →
            AlgebraicGeometry.IsH1RegularImmersion snd.left :=
  sorry

/-- A quasi-regular immersion of algebraic spaces is an immersion whose
étale-on-target represented pullbacks are quasi-regular immersions of
schemes. -/
theorem IsQuasiRegularImmersion.spec {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsQuasiRegularImmersion i] :
    IsImmersion i ∧
      ∀ {V W : Over S} (b : yoneda.obj V ⟶ X.functorOfPoints)
        (fst : yoneda.obj W ⟶ Z.functorOfPoints) (snd : W ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf b →
          IsPullback fst (yoneda.map snd) i b →
            AlgebraicGeometry.IsQuasiRegularImmersion snd.left :=
  sorry

/-- The identity morphism of an algebraic space is a Koszul-regular immersion. -/
instance IsKoszulRegularImmersion.id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsKoszulRegularImmersion (𝟙 X) :=
  sorry

/-- The identity morphism of an algebraic space is an `H₁`-regular immersion. -/
instance IsH1RegularImmersion.id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsH1RegularImmersion (𝟙 X) :=
  sorry

/-- The identity morphism of an algebraic space is a quasi-regular immersion. -/
instance IsQuasiRegularImmersion.id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsQuasiRegularImmersion (𝟙 X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
