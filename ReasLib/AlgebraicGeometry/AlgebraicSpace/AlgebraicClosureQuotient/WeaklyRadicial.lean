/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.Radicial
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Spectrum
public import ReasLib.AlgebraicGeometry.Presheaf.Points
public import ReasLib.AlgebraicGeometry.Sheaf.ReducedInduced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Weak radiciality of the algebraic-closure quotient after base change

The absolute Galois quotient becomes weakly radicial after base change to the
algebraic closure of the rationals, while its reduced identity fibre still
obstructs radiciality.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicNumbers

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- The sheaf fibre product `X ×_{Spec ℚ} Spec algebraicQ` of `toSpec` along the
atlas `Spec algebraicQ ⟶ Spec ℚ`. -/
abbrev toSpec_pullback : Sheaf (Scheme.fppfTopology.over base) (Type 1) :=
  pullback toSpec ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase)

/-- `toSpec_pullback` is the pullback of `toSpec` along the Yoneda image of
`coverToBase`. -/
theorem toSpec_pullback_eq :
    toSpec_pullback =
      pullback toSpec
        ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase) :=
  sorry

/-- The base change `X_{algebraicQ} ⟶ Spec algebraicQ` of `toSpec` along
`Spec algebraicQ ⟶ Spec ℚ`. -/
def toSpec_baseChange :
    toSpec_pullback ⟶
      (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj cover :=
  pullback.snd toSpec
    ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase)

/-- `toSpec_baseChange` is `pullback.snd` of `toSpec` along the Yoneda image of
`coverToBase`. -/
theorem toSpec_baseChange_eq :
    toSpec_baseChange =
      pullback.snd toSpec
        ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase) :=
  sorry

/-- The sheaf fibre `Spec(K) ×_{Spec algebraicQ} X_{algebraicQ}` of
`toSpec_baseChange` along a morphism `Spec(K) ⟶ Spec algebraicQ` over
`Spec ℚ`. -/
abbrev toSpec_baseChange_fibre {K : Type} [Field K] [Algebra ℚ K]
    (σ : Over.mk (FieldExtension.specMap ℚ K) ⟶ cover) :
    Sheaf (Scheme.fppfTopology.over base) (Type 1) :=
  pullback toSpec_baseChange
    ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map σ)

/-- `toSpec_baseChange_fibre σ` is the pullback of `toSpec_baseChange` along
the Yoneda image of `σ`. -/
theorem toSpec_baseChange_fibre_eq {K : Type} [Field K] [Algebra ℚ K]
    (σ : Over.mk (FieldExtension.specMap ℚ K) ⟶ cover) :
    toSpec_baseChange_fibre σ =
      pullback toSpec_baseChange
        ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map σ) :=
  sorry

/-- The base change of the absolute Galois quotient structure morphism along
`Spec algebraicQ ⟶ Spec ℚ` is weakly radicial. -/
@[stacks 049E]
theorem toSpec_baseChange_weaklyRadicial :
    ∀ (K : Type) [Field K] [Algebra ℚ K]
      (σ : Over.mk (FieldExtension.specMap ℚ K) ⟶ cover),
      Nonempty (SpacePresheaf.Points (toSpec_baseChange_fibre σ).obj) ∧
        Subsingleton (SpacePresheaf.Points (toSpec_baseChange_fibre σ).obj) ∧
        ∃ (L : Type) (_ : Field L) (_ : Algebra K L)
          (_ : IsPurelyInseparable K L)
          (ι : (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj
                (FieldExtension.specExtend (FieldExtension.specMap ℚ K) L) ⟶
              toSpec_baseChange_fibre σ),
            Mono ι ∧
              ι ≫ pullback.snd toSpec_baseChange
                    ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map σ) =
                (Scheme.fppfTopology.over base).uliftYoneda.{1}.map
                  (FieldExtension.specExtendToOver (FieldExtension.specMap ℚ K) L) :=
  sorry

/-- The base change of the absolute Galois quotient structure morphism along
`Spec algebraicQ ⟶ Spec ℚ` is not radicial. -/
@[stacks 049E]
theorem toSpec_baseChange_not_radicial :
    ∃ (F : Sheaf (Scheme.fppfTopology.over base) (Type 1))
      (ι : F ⟶ toSpec_baseChange_fibre (𝟙 cover)),
      FppfSheaf.IsReducedInduced ι ∧
        Nonempty (SpacePresheaf.Points F.obj) ∧
        ∀ (L : Type) [Field L] [Algebra algebraicQ L]
          [IsPurelyInseparable algebraicQ L]
          (e : F ≅ (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj
            (FieldExtension.specExtend cover.hom L)),
          e.hom ≫ (Scheme.fppfTopology.over base).uliftYoneda.{1}.map
              (FieldExtension.specExtendToOver cover.hom L) ≠
            ι ≫ pullback.snd toSpec_baseChange
              ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map (𝟙 cover)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
