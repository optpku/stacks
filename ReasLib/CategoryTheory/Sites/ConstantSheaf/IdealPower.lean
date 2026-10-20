module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.Category.CommRingCat.IdealPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant sheaves of ideal-power quotients

This file constructs the inverse systems of constant module and commutative
ring sheaves associated to the quotients `R / I ^ n`.  The two views share the
same explicit quotient transition maps and are independent of any geometric
realization of the site.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {R : Type w} [CommRing R]

section Module

variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]

/-- The `n`th quotient `R / I ^ n`, regarded as an `R`-module. -/
abbrev idealPowerQuotientSequence (I : Ideal R) (n : ℕ) : ModuleCat.{w} R :=
  ModuleCat.of R (R ⧸ I ^ n)

/-- The transition map `R / I ^ (n + 1) ⟶ R / I ^ n` in the module
ideal-power tower. -/
abbrev idealPowerQuotientTransition (I : Ideal R) (n : ℕ) :
    idealPowerQuotientSequence I (n + 1) ⟶ idealPowerQuotientSequence I n :=
  ModuleCat.ofHom
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).toLinearMap

/-- The inverse system `n ↦ R / I ^ n` in `ModuleCat R`. -/
abbrev idealPowerQuotientSystem (I : Ideal R) : ℕᵒᵖ ⥤ ModuleCat.{w} R :=
  Functor.ofOpSequence (idealPowerQuotientTransition I)

/-- The inverse system of constant module sheaves with values `R / I ^ n`. -/
@[stacks 093M "module quotient tower"]
abbrev constantIdealPowerQuotientSheafSystem (I : Ideal R) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R) :=
  idealPowerQuotientSystem I ⋙ constantSheaf J (ModuleCat.{w} R)

/-- The constant module sheaf with value `R / I`. -/
abbrev constantIdealQuotientSheaf (I : Ideal R) : Sheaf J (ModuleCat.{w} R) :=
  (constantIdealPowerQuotientSheafSystem J I).obj (op 1)

end Module

section CommRing

variable (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{w}]

/-- The `n`th quotient `R / I ^ n`, retaining its commutative ring
structure. -/
abbrev idealPowerQuotientRing (I : Ideal R) (n : ℕ) : CommRingCat.{w} :=
  CommRingCat.IdealPower.stage I n

/-- The transition map `R / I ^ (n + 1) ⟶ R / I ^ n` as a commutative
ring homomorphism. -/
abbrev idealPowerQuotientRingTransition (I : Ideal R) (n : ℕ) :
    idealPowerQuotientRing I (n + 1) ⟶ idealPowerQuotientRing I n :=
  CommRingCat.IdealPower.step I n

/-- The inverse system `n ↦ R / I ^ n` in commutative rings. -/
abbrev idealPowerQuotientRingSystem (I : Ideal R) : ℕᵒᵖ ⥤ CommRingCat.{w} :=
  CommRingCat.IdealPower.system I

/-- The inverse system of constant commutative ring sheaves with values `R / I ^ n`. -/
@[stacks 093M "commutative ring quotient tower"]
abbrev constantIdealPowerQuotientRingSheafSystem (I : Ideal R) :
    ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w} :=
  idealPowerQuotientRingSystem I ⋙ constantSheaf J CommRingCat.{w}

/-- The constant commutative ring sheaf with value `R / I`. -/
abbrev constantIdealQuotientRingSheaf (I : Ideal R) : Sheaf J CommRingCat.{w} :=
  (constantIdealPowerQuotientRingSheafSystem J I).obj (op 1)

end CommRing

namespace ConstantSheaf.IdealPower

/-- The `n`th ideal subquotient `I / I ^ n`, with `I ^ n` understood
inside `I` by pullback along the inclusion `I ⟶ R`.  At `n = 0` this is the
zero module. -/
abbrev subquotient (I : Ideal R) (n : ℕ) : ModuleCat.{w} R :=
  ModuleCat.of R (I ⧸ Submodule.comap I.subtype (I ^ n))

/-- The containment needed to descend the identity of `I` to the transition
map `I / I ^ (n + 1) ⟶ I / I ^ n`. -/
theorem subquotientTransition_le (I : Ideal R) (n : ℕ) :
    Submodule.comap I.subtype (I ^ (n + 1)) ≤
      Submodule.comap LinearMap.id (Submodule.comap I.subtype (I ^ n)) := sorry

/-- The transition map `I / I ^ (n + 1) ⟶ I / I ^ n`. -/
abbrev subquotientTransition (I : Ideal R) (n : ℕ) :
    subquotient I (n + 1) ⟶ subquotient I n :=
  ModuleCat.ofHom <| Submodule.mapQ _ _ LinearMap.id
    (subquotientTransition_le I n)

/-- The inverse system `n ↦ I / I ^ n` of `R`-modules. -/
abbrev subquotientSystem (I : Ideal R) : ℕᵒᵖ ⥤ ModuleCat.{w} R :=
  Functor.ofOpSequence (subquotientTransition I)

/-- The natural inclusion of the ideal subquotient system
`I / I ^ n` into the ring quotient system `R / I ^ n`. -/
noncomputable def subquotientToQuotient (I : Ideal R) :
    subquotientSystem I ⟶ idealPowerQuotientSystem I where
  app n := ModuleCat.ofHom <| Submodule.mapQ
    (Submodule.comap I.subtype (I ^ n.unop)) (I ^ n.unop) I.subtype le_rfl
  naturality := sorry

variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]

/-- The inverse system of constant module sheaves with values `I / I ^ n`. -/
@[stacks 093M "completed ideal system"]
abbrev constantSubquotientSystem (I : Ideal R) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} R) :=
  subquotientSystem I ⋙ constantSheaf J (ModuleCat.{w} R)

/-- The natural inclusion of constant ideal-subquotient sheaves into the
constant ring-quotient sheaves. -/
noncomputable def constantSubquotientToQuotient (I : Ideal R) :
    constantSubquotientSystem J I ⟶ constantIdealPowerQuotientSheafSystem J I :=
  Functor.whiskerRight (subquotientToQuotient I)
    (constantSheaf J (ModuleCat.{w} R))

end ConstantSheaf.IdealPower

end CategoryTheory
