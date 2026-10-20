module

public import ReasLib.AlgebraicGeometry.RelativeCycle.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Pushforward of families of `r`-cycles on fibres along a thickening over a
common base is a bijection. -/
theorem pushforward_bijective {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ) :
    Function.Bijective (fun α : fX.FiberCycleFamily r ↦ pushforward fX' i hc α) := sorry

/-- A thickening between schemes locally of finite type over a locally
Noetherian base induces a bijection on relative `r`-cycles. -/
@[stacks 0H5E]
theorem groupPushforward_bijective {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsThickening i]
    (hc : i ≫ fX' = fX) (r : ℕ) :
    Function.Bijective (groupPushforward fX fX' i hc r) := sorry

end AlgebraicGeometry.RelativeCycle
