/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap76.Definition_76_9_1_Arrow
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder
public import stacks_project.Chap76.Lemma_76_18_1_Thickening

/-!
# Base change of thickenings of algebraic spaces

The fibre product of a thickening of algebraic spaces along an arbitrary
morphism is again a thickening, and the resulting square is a morphism of
thickenings. First-order and finite-order thickenings are likewise stable
under this base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsThickening

/-- The base-change projection `pullback.snd i f'` of a thickening
`i : Y ⟶ Y'` is a thickening. -/
instance pullbackSnd {S : Scheme.{u}} {Y Y' X' : AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y') [IsThickening i] :
    IsThickening (pullback.snd i f') :=
  sorry

end IsThickening

namespace Thickening

/-- A pullback square of a thickening of algebraic spaces induces a morphism
from the pullback thickening to the original thickening. -/
noncomputable def pullbackHom {S : Scheme.{u}} {Y Y' X' : AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y') [IsThickening i] :
    Thickening.of (pullback.snd i f') ⟶ Thickening.of i :=
  Thickening.homMk (pullback.fst i f') f' pullback.condition

/-- The closed-subspace leg of `pullbackHom i f'` is the first projection of
the fibre product. -/
theorem pullbackHom_left {S : Scheme.{u}} {Y Y' X' : AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y') [IsThickening i] :
    (pullbackHom i f').left = pullback.fst i f' :=
  sorry

/-- The ambient-space leg of `pullbackHom i f'` is the morphism
`f' : X' ⟶ Y'`. -/
theorem pullbackHom_right {S : Scheme.{u}} {Y Y' X' : AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y') [IsThickening i] :
    (pullbackHom i f').right = f' :=
  sorry

end Thickening

namespace IsFirstOrderThickening

/-- The pullback of a first-order thickening of algebraic spaces is a
first-order thickening. -/
instance pullbackSnd {S : Scheme.{u}} {Y Y' X' : AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y') [IsFirstOrderThickening i] :
    IsFirstOrderThickening (pullback.snd i f') :=
  sorry

end IsFirstOrderThickening

namespace IsFiniteOrderThickening

/-- The pullback of a finite-order thickening of algebraic spaces is a
finite-order thickening. -/
instance pullbackSnd {S : Scheme.{u}} {Y Y' X' : AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y') [IsFiniteOrderThickening i] :
    IsFiniteOrderThickening (pullback.snd i f') :=
  sorry

end IsFiniteOrderThickening

end AlgebraicGeometry.AlgebraicSpace
