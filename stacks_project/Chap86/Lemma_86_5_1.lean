/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.Lemma_86_5_1_BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

/- Lemma 86.5.1 (1): in cartesian Tor-independent diagram 86.4.0.1 of algebraic
spaces over S, with g a morphism of affine schemes and f proper, flat, and of
finite presentation, the 86.4.1.1 mate L(g')^* a(K) ⟶ a'(Lg^* K) is an
isomorphism for all K : DerivedQCoh Y. -/
@[stacks 0E5I] #check mapOfRight_app_isIso_of_flat

/- Lemma 86.5.1 (2): in cartesian Tor-independent diagram 86.4.0.1 of algebraic
spaces over S, with g a morphism of affine schemes, f proper and perfect, and Y
Noetherian, the 86.4.1.1 mate L(g')^* a(K) ⟶ a'(Lg^* K) is an isomorphism for
all K : DerivedQCoh Y. -/
@[stacks 0E5I] #check mapOfRight_app_isIso_of_perfect

/- Lemma 86.5.1 (3): in cartesian Tor-independent diagram 86.4.0.1 of algebraic
spaces over S, with g a morphism of affine schemes of finite Tor dimension, f
proper, and Y Noetherian, the 86.4.1.1 mate L(g')^* a(K) ⟶ a'(Lg^* K) is an
isomorphism for all K : DerivedQCoh Y with K.obj.IsBoundedBelow. -/
@[stacks 0E5I] #check mapOfRight_app_isIso_of_finiteTorDimension
