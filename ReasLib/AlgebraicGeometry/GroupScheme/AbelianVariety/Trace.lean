/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Trace
public import ReasLib.Algebra.Group.Torsion.Map
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.GroupScheme.RationalPoints

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AbelianVariety

variable {k : Type u} [Field k]
variable {A : SchemeOverField k} [GrpObj A] [AbelianVariety A]

/-- Postcomposition with a group-scheme endomorphism of an abelian variety. -/
def homCompRight (f : A ⟶ A) [IsMonHom f] :
    (𝟙_ (SchemeOverField k) ⟶ A) →* (𝟙_ (SchemeOverField k) ⟶ A) where
  toFun p := p ≫ f
  map_one' := MonObj.one_comp f
  map_mul' p q := MonObj.mul_comp p q f

/-- The additive endomorphism induced on the group of rational points. -/
def rationalPointsMap (f : A ⟶ A) [IsMonHom f] :
    SchemeOverField.rationalPoints A →+ SchemeOverField.rationalPoints A :=
  (homCompRight f).toAdditive

/-- Rational `ℓ`-torsion of an abelian variety is a `ZMod ℓ`-module. -/
instance instModule_rationalTorsion (ℓ : ℕ) [NeZero ℓ] :
    Module (ZMod ℓ)
      (AddSubgroup.torsionBy (SchemeOverField.rationalPoints A) (ℓ : ℤ)) :=
  AddSubgroup.torsionBy.zmodModule

/-- The linear action induced on rational `ℓ`-torsion by an abelian-variety endomorphism. -/
def rationalTorsionMap (f : A ⟶ A) [IsMonHom f] (ℓ : ℕ) [NeZero ℓ] :
    Module.End (ZMod ℓ)
      (AddSubgroup.torsionBy (SchemeOverField.rationalPoints A) (ℓ : ℤ)) :=
  AddMonoidHom.toZModLinearMap ℓ
    ((rationalPointsMap f).torsionByMap (ℓ : ℤ))

/-- On rational points, the torsion action is induced by postcomposition. -/
theorem rationalTorsionMap_apply (f : A ⟶ A) [IsMonHom f] (ℓ : ℕ) [NeZero ℓ]
    (p : AddSubgroup.torsionBy (SchemeOverField.rationalPoints A) (ℓ : ℤ)) :
    (rationalTorsionMap f ℓ p).val = rationalPointsMap f p.val := sorry

/-- The integer trace characterized by all invertible modular torsion traces. -/
def endomorphismTrace (f : A ⟶ A) [IsMonHom f] [IsAlgClosed k] : ℤ :=
  Classical.epsilon fun t : ℤ ↦
    ∀ (ℓ : ℕ) [NeZero ℓ], IsUnit (ℓ : k) →
      LinearMap.trace (ZMod ℓ) _
          (rationalTorsionMap f ℓ) = (t : ZMod ℓ)

/-- The integer trace reduces modulo every unit `ℓ` in the field. -/
theorem endomorphismTrace_spec (f : A ⟶ A) [IsMonHom f] [IsAlgClosed k]
    (ℓ : ℕ) [NeZero ℓ] (hℓ : IsUnit (ℓ : k)) :
    LinearMap.trace (ZMod ℓ) _ (rationalTorsionMap f ℓ) =
      (endomorphismTrace f : ZMod ℓ) := sorry

/-- An integer with all modular torsion traces equals the integer trace. -/
theorem endomorphismTrace_unique (f : A ⟶ A) [IsMonHom f] [IsAlgClosed k] (t : ℤ)
    (ht : ∀ (ℓ : ℕ) [NeZero ℓ], IsUnit (ℓ : k) →
      LinearMap.trace (ZMod ℓ) _ (rationalTorsionMap f ℓ) = (t : ZMod ℓ)) :
    t = endomorphismTrace f := sorry

end AlgebraicGeometry.AbelianVariety
