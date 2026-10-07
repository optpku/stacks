module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import stacks_project.Chap61.Definition_61_28_1_Completion
public import stacks_project.Chap61.Lemma_61_28_6
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.28.7

A derived-complete sheaf of `Λ`-modules on the pro-étale site of a weakly
contractible affine scheme, with locally constant finite-type reduction
modulo `I`, is an epimorphic image of a finite coproduct of copies of
`underline(Λ)^∧`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived (constantCoefficientRing)

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
variable [HasWeakSheafify (topology X) CommRingCat.{w}]
variable [HasWeakSheafify (topology X) RingCat.{w}]
variable [HasWeakSheafify (topology X) AddCommGrpCat.{w}]
variable [(topology X).WEqualsLocallyBijective RingCat.{w}]
variable [(topology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [(topology X).PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{u + 1, w}]
variable [LocallySmall
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [WellPowered
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]

/-- Finite discrete diagrams of abelian groups have colimits. -/
instance instHasColimitsOfShapeDiscreteFinAddCommGrp (n : ℕ) :
    HasColimitsOfShape (Discrete (Fin n)) AddCommGrpCat.{w} :=
  AddCommGrpCat.hasColimitsOfShape

/-- Finite discrete diagrams of `Λ`-modules have colimits. -/
instance instHasColimitsOfShapeDiscreteFinModuleCat (n : ℕ) :
    HasColimitsOfShape (Discrete (Fin n)) (ModuleCat.{w} Λ) :=
  inferInstance

/-- Finite discrete diagrams of presheaves of `Λ`-modules have colimits. -/
instance instHasColimitsOfShapeDiscreteFinPresheafModuleCat (n : ℕ) :
    HasColimitsOfShape (Discrete (Fin n)) (X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ) :=
  functorCategoryHasColimitsOfShape

/-- Finite discrete diagrams of sheaves of `Λ`-modules have colimits. -/
instance instHasColimitsOfShapeDiscreteFinSheafModuleCat (n : ℕ) :
    HasColimitsOfShape (Discrete (Fin n)) (Sheaf (topology X) (ModuleCat.{w} Λ)) :=
  Sheaf.instHasColimitsOfShape

/-- Lemma 61.28.7: if `X` is a weakly contractible affine scheme, `Λ` is a Noetherian
ring, `I ⊆ Λ` is an ideal, and `F` is a derived-complete sheaf of `Λ`-modules on
`X_proétale` with `F / I F` a locally constant sheaf of finite-type `Λ / I`-modules,
then there exist `t : ℕ` and an epimorphism
`(∐ fun _ : Fin t ↦ lambdaHat (topology X) I) ⟶ F`.

Weakly contractible affine is `IsAffine` together with
`(topology X).IsWeaklyContractible (ProEt.mk (𝟙 X))`. The completed constant sheaf
`underline(Λ)^∧` is `lambdaHat`. The finite coproduct `(underline(Λ)^∧)^⊕t` is the
coproduct of `t` copies of `lambdaHat`. The quotient `F / I F` is
`IdealPower.quotient I F 1`. Locally constant of finite type as `Λ / I`-modules
is `IsFiniteTypeLocallyConstantModule` on that quotient. Surjectivity is `Epi`. -/
@[stacks 09BZ]
theorem exists_epi_from_lambdaHat
    [IsAffine X] [IsNoetherianRing Λ]
    [(topology X).IsWeaklyContractible (ProEt.mk (𝟙 X))]
    (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ))
    (hF : DerivedComplete.IsDerivedComplete I F)
    (hquot : IsFiniteTypeLocallyConstantModule (IdealPower.quotient I F 1)) :
    ∃ (t : ℕ) (π : (∐ fun _ : Fin t ↦ lambdaHat (topology X) I) ⟶ F),
      Epi π :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
