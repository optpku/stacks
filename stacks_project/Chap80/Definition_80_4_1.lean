/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 80.4.1: let `S` be a scheme. Let `a : F ⟶ G` be a morphism of
presheaves on `(Sch/S)_fppf` which is representable by algebraic spaces. Let
`P` be a property of morphisms of algebraic spaces. We say that `a` has
property `P` if for every scheme `U` over `S` and Yoneda section
`ξ : yoneda.obj U ⟶ G`, the resulting morphism of algebraic spaces
`U ×_G F ⟶ U` has property `P`. In the Stacks Project's applications, `P` is
stable under base change and fppf local on the base (see Definition 74.10.1 /
tag 03YH); those hypotheses describe the intended usage, not extra binders in
this definition. -/
@[stacks 03XZ] #check (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces : ∀ {S : AlgebraicGeometry.Scheme.{u}}, CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S) → CategoryTheory.MorphismProperty ((CategoryTheory.Over S)ᵒᵖ ⥤ Type u))
