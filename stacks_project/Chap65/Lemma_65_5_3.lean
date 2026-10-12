/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 65.5.3: let `S` be a scheme and let `X`, `Y` be objects of `Over S`.
Let `f : X ⟶ Y` be a morphism of schemes over `S`, and let `P` be a property of
morphisms of schemes that is stable under base change and fppf local at the
target. Then the Yoneda
transformation `yoneda.map f : yoneda.obj X ⟶ yoneda.obj Y` has property `P`
in the sense of Definition 65.5.1 if and only if the underlying scheme morphism
`f.left` has property `P`. -/
@[stacks 02WJ] #check
  (AlgebraicGeometry.Scheme.representableMorphismProperty_yoneda_map_iff :
    ∀ {S : Scheme.{u}} {X Y : Over S} (P : MorphismProperty Scheme.{u})
      [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage] (f : X ⟶ Y),
      Scheme.representableMorphismProperty S P (yoneda.map f) ↔ P f.left)
