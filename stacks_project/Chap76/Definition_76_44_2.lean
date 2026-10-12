/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_44_2_RegularImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 76.44.2 (1): a morphism `i : X ⟶ Y` of algebraic spaces over a scheme `S`
is a Koszul-regular immersion if `i` is representable and the equivalent conditions of
Lemma 76.44.1 hold with `P` = Koszul-regular immersion. -/
@[stacks 06BN] #check (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

/- Definition 76.44.2 (2): a morphism `i : X ⟶ Y` of algebraic spaces over a scheme `S`
is an `H₁`-regular immersion if `i` is representable and the equivalent conditions of
Lemma 76.44.1 hold with `P` = `H₁`-regular immersion. -/
@[stacks 06BN] #check (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

/- Definition 76.44.2 (3): a morphism `i : X ⟶ Y` of algebraic spaces over a scheme `S`
is a quasi-regular immersion if `i` is representable and the equivalent conditions of
Lemma 76.44.1 hold with `P` = quasi-regular immersion. -/
@[stacks 06BN] #check (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)
