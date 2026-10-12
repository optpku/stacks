/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.RingTheory.AdicCompletion.Map
public import ReasLib.RingTheory.Completion.FormallySmoothLift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Completed Base Change of Complete Local Rings

@stack 07NS
-/

@[expose] public section

noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v w x

namespace AdicCompletion.BaseChange

/-- The ideal defining completed base change: the image of `maximalIdeal A'` under the right
tensor-factor map `A' → C ⊗[A] A'`. -/
@[stacks 07NS "base-changed completion ideal"]
abbrev ideal (A : Type u) (A' : Type v) [CommRing A] [CommRing A'] [Algebra A A']
    [IsLocalRing A'] (C : Type x) [CommRing C] [Algebra A C] :
    Ideal (C ⊗[A] A') :=
  Ideal.map
    (Algebra.TensorProduct.includeRight (R := A) (A := C) (B := A')).toRingHom
    (maximalIdeal A')

/-- The completion of `C ⊗[A] A'` along the image of `maximalIdeal A'`. -/
@[stacks 07NS "base-changed completion ring"]
abbrev ring (A : Type u) (A' : Type v) [CommRing A] [CommRing A'] [Algebra A A']
    [IsLocalRing A'] (C : Type x) [CommRing C] [Algebra A C] :=
  AdicCompletion (ideal A A' C) (C ⊗[A] A')

/-- The tensor-product map `C ⊗[A] A' → B` induced by compatible maps `C → B` and
`A' → B`. -/
@[stacks 07NS "base-changed tensor-product target map"]
noncomputable def toTarget (A : Type u) (A' : Type v) (B : Type w) (C : Type x)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' B] [Algebra C B]
    [IsScalarTower A A' B] [IsScalarTower A C B] :
    C ⊗[A] A' →+* B :=
  (Algebra.TensorProduct.productMap
    ((Algebra.ofId C B).restrictScalars A)
    ((Algebra.ofId A' B).restrictScalars A)).toRingHom

/-- The tensor-product map is continuous from the `maximalIdeal A'`-adic base-change topology to
the `maximalIdeal B`-adic topology. -/
theorem toTarget_adicContinuous
    {A : Type u} {A' : Type v} {B : Type w} {C : Type x}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' B] [Algebra C B]
    [IsScalarTower A A' B] [IsScalarTower A C B]
    [IsLocalRing A'] [IsLocalRing B] [IsLocalHom (algebraMap A' B)] :
    (toTarget A A' B C).AdicContinuous (ideal A A' C) (maximalIdeal B) := sorry

/-- The canonical map from completed base change to a complete local target. -/
@[stacks 07NS "completion base-change comparison map"]
noncomputable def map (A : Type u) (A' : Type v) (B : Type w) (C : Type x)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' B] [Algebra C B]
    [IsScalarTower A A' B] [IsScalarTower A C B]
    [IsLocalRing A'] [IsCompleteLocalRing B] [IsLocalHom (algebraMap A' B)] :
    ring A A' C →+* B :=
  (AdicCompletion.ofAlgEquiv (maximalIdeal B)).symm.toRingHom.comp
    (toTarget_adicContinuous (A := A) (A' := A') (B := B) (C := C)).completionMap

/-- The completed base-change map extends the tensor-product map before completion. -/
theorem map_comp_algebraMap
    {A : Type u} {A' : Type v} {B : Type w} {C : Type x}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' B] [Algebra C B]
    [IsScalarTower A A' B] [IsScalarTower A C B]
    [IsLocalRing A'] [IsCompleteLocalRing B] [IsLocalHom (algebraMap A' B)] :
    (map A A' B C).comp (algebraMap (C ⊗[A] A') (ring A A' C)) =
      toTarget A A' B C := sorry

section Source

variable {A : Type u} {A' : Type v} {B : Type w}
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsNoetherianRing A'] [IsCompleteLocalRing A']
variable [IsNoetherianRing B] [IsCompleteLocalRing B]
variable [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A' B)]

/-- Remark 15.40.7 (1) (07NS): if `A → A'` identifies residue fields and the closed fiber of
`A' → B` is adically formally smooth, there is an adically formally smooth complete local
`A`-algebra `C` whose canonical completed base change maps surjectively to `B`. -/
@[stacks 07NS "Remark 15.40.7 (1)"]
theorem existsFormallySmoothLift
    (hκ : Function.Bijective (ResidueField.map (algebraMap A A')))
    (hfs :
      (algebraMap (ResidueField A') (Ideal.Fiber (maximalIdeal A') B)).formally_smooth_for_adic
        (maximalIdeal (Ideal.Fiber (maximalIdeal A') B))) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra A C) (_ : IsNoetherianRing C)
      (_ : IsCompleteLocalRing C) (_ : IsLocalHom (algebraMap A C)) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (_ : IsLocalHom (algebraMap C B)),
      (algebraMap A C).formally_smooth_for_adic (maximalIdeal C) ∧
        Function.Surjective (map A A' B C) := sorry

/-- Remark 15.40.7 (2) (07NS): if `A → A'` is surjective, surjectivity of the completed
base-change map forces `C → B` to be surjective. -/
@[stacks 07NS "Remark 15.40.7 (2)"]
theorem toTargetSurjectiveOfBaseSurjective
    {C : Type x} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hmap : Function.Surjective (map A A' B C))
    (hbase : Function.Surjective (algebraMap A A')) :
    Function.Surjective (algebraMap C B) := sorry

/-- Remark 15.40.7 (3) (07NS): if `A'` is finite over `A`, surjectivity of the completed
base-change map makes `B` finite over `C`. -/
@[stacks 07NS "Remark 15.40.7 (3)"]
theorem targetFiniteOfBaseFinite
    {C : Type x} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hmap : Function.Surjective (map A A' B C)) [Module.Finite A A'] :
    Module.Finite C B := sorry

/-- Remark 15.40.7 (4) (07NS): flatness of `A' -> B` upgrades a surjective completed
base-change map to a bijection. -/
@[stacks 07NS "Remark 15.40.7 (4)"]
theorem mapBijectiveOfFlat
    {C : Type x} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hflat : (algebraMap A' B).Flat)
    (hmap : Function.Surjective (map A A' B C)) :
    Function.Bijective (map A A' B C) := sorry

end Source

end AdicCompletion.BaseChange
