/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Monotonicity
import StacksCheckRecall

/-!
# Monotonicity of transferred morphism properties of algebraic spaces

If `P ≤ P'` as morphism properties of algebraic spaces over `S`, then a
morphism of presheaves representable by algebraic spaces that has `P` also
has `P'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.4.5: let `S` be a scheme. Let `F, G : (Over S)ᵒᵖ ⥤ Type u` and
let `a : F ⟶ G` be representable by algebraic spaces. Let `P`, `P'` be
morphism properties of algebraic spaces over `S` as in Definition 80.4.1,
and suppose `P f → P' f` for every morphism `f` of algebraic spaces over
`S`. If `a` has property `P`, then `a` has property `P'`. Equivalently, the
transfer `relativeAlgebraicSpaces` is monotone along `P ≤ P'`, so the
Yoneda pullbacks `pullbackHom : U ×_G F ⟶ U` inherit `P'` from `P`. -/
@[stacks 0AM1] #check
  (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces.monotone :
    ∀ {S : Scheme.{u}} {P P' : MorphismProperty (AlgebraicSpace S)},
      P ≤ P' → relativeAlgebraicSpaces P ≤ relativeAlgebraicSpaces P')

end AlgebraicGeometry.AlgebraicSpace
