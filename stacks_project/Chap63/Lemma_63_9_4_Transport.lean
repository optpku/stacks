/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.InverseImage.Isomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Transport
public import stacks_project.Chap63.Lemma_63_8_5_Pullback
public import stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_8_5_Comparison

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Compactification

universe u

variable {Y : Scheme.{u}} {X : Over Y} {P Q : Of Y X} (e : P ≅ Q)

/- Lemma 63.9.4: an isomorphism of fixed-interior compactifications identifies the ambients. -/
#check (AlgebraicGeometry.Scheme.Compactification.Of.ambientIso e :
  P.obj.right.left ≅ Q.obj.right.left)

end
