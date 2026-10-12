/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.pullback :
  ∀ {Z X Z' X' : Scheme.{u}}
      {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {f : X' ⟶ X}
      [IsImmersion i'] [IsImmersion i],
    IsPullback g i' i f →
      Scheme.Hom.VirtualNormalBundle i → Scheme.Hom.VirtualNormalBundle i')
