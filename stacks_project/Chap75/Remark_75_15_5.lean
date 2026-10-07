module

public import stacks_project.Chap75.Lemma_75_6_4_Pushforward
public import stacks_project.Chap75.Remark_75_15_5_Conservative
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Remark 75.15.5 (1): for a quasi-compact and quasi-separated morphism of algebraic
spaces, derived pushforward reflects zero objects exactly when it reflects
isomorphisms. -/
@[stacks 0E4R] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward.reflectsZero_iff_reflectsIsomorphisms :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
      (∀ K : DerivedQCoh X, IsZero ((pushforward f).obj K) ↔ IsZero K) ↔
        (pushforward f).ReflectsIsomorphisms)

/- Remark 75.15.5 (2): for a weak generator on the target, derived pushforward reflects
zero objects exactly when its derived pullback is a weak generator. -/
@[stacks 0E4R] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward.reflectsZero_iff_pullback_isWeakGenerator :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      (E : DerivedQCoh Y),
      IsWeakGenerator E →
        ((∀ K : DerivedQCoh X, IsZero ((pushforward f).obj K) ↔ IsZero K) ↔
          IsWeakGenerator ((DerivedQCoh.pullback f).obj E)))

/- Remark 75.15.5 (3): derived pushforward along an affine morphism of algebraic spaces
reflects isomorphisms. -/
@[stacks 0E4R] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward.reflectsIsomorphisms_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f],
      (pushforward f).ReflectsIsomorphisms)

/- Remark 75.15.5 (4): derived pushforward along an open immersion of algebraic spaces
reflects isomorphisms. -/
@[stacks 0E4R] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward.reflectsIsomorphisms_of_isOpenImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      [IsOpenImmersion f],
      (pushforward f).ReflectsIsomorphisms)

/- Remark 75.15.5 (5): conservativity of derived pushforward is stable under composition. -/
@[stacks 0E4R] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward.reflectsIsomorphisms_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
      [(pushforward f).ReflectsIsomorphisms] [(pushforward g).ReflectsIsomorphisms],
      (pushforward (f ≫ g)).ReflectsIsomorphisms)
