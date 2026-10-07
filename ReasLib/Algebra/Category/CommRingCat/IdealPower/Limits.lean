module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import ReasLib.Algebra.Category.CommRingCat.IdealPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Limits of Ideal-Power Quotient Rings

Adic completeness identifies a ring with the inverse limit of its positive ideal-power
quotients.  The `LimitCone` below retains the canonical quotient cone itself, so downstream
restriction-of-scalars constructions use the expected quotient maps definitionally.
@stack 09AV
@stack 09AW
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace CategoryTheory.CommRingCat.IdealPower.Positive

variable {A : Type u} [CommRing A]

/-- The legs of an arbitrary cone over the positive ideal-power system form the compatible family
required by `IsAdicComplete.StrictMono.liftRingHom`. -/
theorem lift_compatible (I : Ideal A) (s : Cone (system I)) (n : ℕ) :
    (Ideal.Quotient.factorPow I
        ((strictMono_id.add_const 1).monotone n.le_succ)).comp
        (s.stageMap (n + 1)).hom =
      (s.stageMap n).hom := sorry

/-- The universal ring homomorphism from a cone vertex to an `I`-adically complete ring. -/
@[stacks 09AV "adic lift from compatible ideal-power quotients",
  stacks 09AW "adic lift from compatible ideal-power quotients"]
noncomputable def lift (I : Ideal A) [IsAdicComplete I A]
    (s : Cone (system I)) : s.pt ⟶ CommRingCat.of A :=
  CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom I (strictMono_id.add_const 1)
      (fun n ↦ (s.stageMap n).hom) (fun {_} ↦ lift_compatible I s _))

/-- The canonical cone from an `I`-adically complete ring to its positive ideal-power quotients
is limiting.  Its universal morphism is `lift I`. -/
@[stacks 09AV "adic ring as an ideal-power inverse limit",
  stacks 09AW "adic ring as an ideal-power inverse limit"]
noncomputable def coneIsLimit (I : Ideal A) [IsAdicComplete I A] :
    IsLimit (cone I) where
  lift s := lift I s
  fac := sorry
  uniq := sorry

/-- The universal morphism selected by `coneIsLimit I` is the adic lift. -/
@[simp]
theorem coneIsLimit_lift (I : Ideal A) [IsAdicComplete I A]
    (s : Cone (system I)) :
    (coneIsLimit I).lift s = lift I s := sorry

/-- The canonical limiting cone of an adically complete ring over its positive ideal-power
quotients. -/
@[stacks 09AV "canonical ideal-power limit cone",
  stacks 09AW "canonical ideal-power limit cone"]
noncomputable def limitCone (I : Ideal A) [IsAdicComplete I A] : LimitCone (system I) where
  cone := cone I
  isLimit := coneIsLimit I

/-- The cone underlying `limitCone I` is the canonical quotient cone. -/
@[simp]
theorem limitCone_cone (I : Ideal A) [IsAdicComplete I A] :
    (limitCone I).cone = cone I := sorry

end CategoryTheory.CommRingCat.IdealPower.Positive
