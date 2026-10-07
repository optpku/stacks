module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant.AdicCompletion
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.IdealPower
public import ReasLib.CategoryTheory.Sites.WeaklyContractible

/-!
# Completed constant sheaves on weakly contractible affine schemes
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

namespace ProEt

/-- A complete module sheaf with constant reductions and finite-type first reduction
on a weakly contractible affine pro-étale site is a completed constant sheaf of a
finite module over the adic completion. -/
theorem exists_iso_constantAdicCompletion
    {X : Scheme.{u}} [IsAffine X]
    [(ProEt.topology X).IsWeaklyContractible (ProEt.mk (𝟙 X))]
    {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{w} Λ)]
    [HasWeakSheafify (ProEt.topology X) RingCat.{w}]
    [(ProEt.topology X).WEqualsLocallyBijective RingCat.{w}]
    [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{w}]
    [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{w}]
    [∀ U : X.ProEt, ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (I : Ideal Λ) (F : Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))
    (h_limit : IsIso (Sheaf.IdealPower.toLimit I F))
    (h_constant : ∀ n : ℕ,
      Sheaf.IsConstant (ProEt.topology X) (Sheaf.IdealPower.quotient I F n.succ))
    (h_finiteType :
      ((Sheaf.IdealPower.quotient I F 1).toConstantModuleSheaf).IsFiniteType) :
    ∃ (M : ModuleCat.{w} (AdicCompletion I Λ)),
        Module.Finite (AdicCompletion I Λ) M ∧
        Nonempty (F ≅ ConstantSheaf.AdicCompletion.ofAdicModule (ProEt.topology X) I M) := sorry

end ProEt

end AlgebraicGeometry.Scheme
