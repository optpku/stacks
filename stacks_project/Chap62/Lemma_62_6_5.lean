module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap62.Definition_62_6_1_Specialization
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_8_2_Operations
public import ReasLib.AlgebraicGeometry.RelativeCycle.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.6.5: if `S` is locally Noetherian and `i : X ⟶ Y` is a closed
immersion of schemes locally of finite type over `S`, then a family `α` of
`r`-cycles on fibres of `X / S` is a relative `r`-cycle if and only if the
pushforward `i_*α` is a relative `r`-cycle on `Y / S`. -/
@[stacks 0H54]
#check (AlgebraicGeometry.RelativeCycle.isRelative_iff_pushforward :
  ∀ {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (i : X ⟶ Y) [IsClosedImmersion i] (hc : i ≫ fY = fX) (r : ℕ)
    (α : fX.FiberCycleFamily r),
    IsRelative α ↔ IsRelative (pushforward fY i hc α))

end AlgebraicGeometry.RelativeCycle
