/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Lemma_67_4_8
public import stacks_project.Chap67.Lemma_67_8_5
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward
public import stacks_project.Chap75.Remark_75_6_3

/-!
# Conservativity of derived pushforward on algebraic spaces

Restricted derived pushforward on complexes with quasi-coherent cohomology
reflects zeros if and only if it reflects isomorphisms, equivalently if and
only if it sends a weak generator of the target to a weak generator of the
source. Affine morphisms, open immersions, and composites of such are
conservative.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward

/-- Derived pushforward along a quasi-compact, quasi-separated morphism of algebraic
spaces reflects zero objects if and only if it reflects isomorphisms. -/
theorem reflectsZero_iff_reflectsIsomorphisms {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (∀ K : DerivedQCoh X, IsZero ((pushforward f).obj K) ↔ IsZero K) ↔
      (pushforward f).ReflectsIsomorphisms := sorry

/-- If an object weakly generates the target, derived pushforward reflects zero objects
exactly when its derived pullback weakly generates the source. -/
theorem reflectsZero_iff_pullback_isWeakGenerator {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedQCoh Y) (hE : IsWeakGenerator E) :
    (∀ K : DerivedQCoh X, IsZero ((pushforward f).obj K) ↔ IsZero K) ↔
      IsWeakGenerator ((AlgebraicSpace.DerivedQCoh.pullback f).obj E) := sorry

/-- Derived pushforward along a quasi-compact open immersion of algebraic spaces
reflects isomorphisms. -/
instance reflectsIsomorphisms_of_isOpenImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsOpenImmersion f] :
    (pushforward f).ReflectsIsomorphisms := sorry

/-- Conservativity of derived pushforward is stable under composition of quasi-compact,
quasi-separated morphisms of algebraic spaces. -/
instance reflectsIsomorphisms_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [(pushforward f).ReflectsIsomorphisms] [(pushforward g).ReflectsIsomorphisms] :
    (pushforward (f ≫ g)).ReflectsIsomorphisms := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward
