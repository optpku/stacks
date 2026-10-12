/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Quadruple

/-!
# Common-multiple comparisons of relative projective quadruples

Positive-degree relative projective quadruples can be compared after restricting both Veronese
presentations to a common multiple. The comparison uses the canonical tensor-power map induced
by a single isomorphism of the powered line bundles.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeProjQuadruple

variable {S : Scheme.{u}}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
variable {T : Scheme.{u}}

/-- Restrict one homogeneous component of a relative projective quadruple to a specified common
multiple and rebracket its target as a tensor power of the powered line bundle. -/
noncomputable def commonMultipleDegreeMap
    (q : RelativeProjQuadruple 𝒜 T) (n a : ℕ)
    (hn : n = a * q.degree) (m : ℕ) :
    𝒜 (Int.ofNat (m * n)) ⟶
      (Scheme.Modules.pushforward q.morphism).obj
        (RingedSpace.TensorPower.sheaf
          (RingedSpace.TensorPower.sheaf q.lineBundle a) m) :=
  eqToHom
      (congrArg (fun k : ℤ ↦ 𝒜 k) <|
        congrArg Int.ofNat <|
          (congrArg (fun k : ℕ ↦ m * k) hn).trans
            (Nat.mul_assoc m a q.degree).symm) ≫
    q.psi (m * a) ≫
      (Scheme.Modules.pushforward q.morphism).map
        (RingedSpace.TensorPower.mulIso q.lineBundle a m).inv

/-- Two relative projective quadruples are compatible at a specified common multiple when their
structure morphisms agree and an isomorphism of the powered line bundles identifies every
restricted homogeneous map through its canonical tensor powers. -/
def CompatibleAt
    (q q' : RelativeProjQuadruple 𝒜 T) (n a a' : ℕ)
    (hn : n = a * q.degree) (hn' : n = a' * q'.degree) : Prop :=
  ∃ morphism_eq : q.morphism = q'.morphism,
    ∃ beta : RingedSpace.TensorPower.sheaf q.lineBundle a ≅
        RingedSpace.TensorPower.sheaf q'.lineBundle a',
      ∀ m : ℕ,
        HEq
          (commonMultipleDegreeMap q n a hn m ≫
            (Scheme.Modules.pushforward q.morphism).map
              (RingedSpace.TensorPower.mapIso beta m).hom)
          (commonMultipleDegreeMap q' n a' hn' m)

/-- Compatibility at a specified common multiple is characterized by equality of the structure
morphisms and a powered-line-bundle isomorphism intertwining every homogeneous component. -/
theorem compatibleAt_iff
    (q q' : RelativeProjQuadruple 𝒜 T) (n a a' : ℕ)
    (hn : n = a * q.degree) (hn' : n = a' * q'.degree) :
    CompatibleAt q q' n a a' hn hn' ↔
      ∃ morphism_eq : q.morphism = q'.morphism,
        ∃ beta : RingedSpace.TensorPower.sheaf q.lineBundle a ≅
            RingedSpace.TensorPower.sheaf q'.lineBundle a',
          ∀ m : ℕ,
            HEq
              (commonMultipleDegreeMap q n a hn m ≫
                (Scheme.Modules.pushforward q.morphism).map
                  (RingedSpace.TensorPower.mapIso beta m).hom)
              (commonMultipleDegreeMap q' n a' hn' m) :=
  Iff.rfl

/-- Two relative projective quadruples are compatible at the least common multiple of their
positive degrees. -/
def CompatibleAtLcm (q q' : RelativeProjQuadruple 𝒜 T) : Prop :=
  ∃ a a',
    ∃ hn : Nat.lcm q.degree q'.degree = a * q.degree,
      ∃ hn' : Nat.lcm q.degree q'.degree = a' * q'.degree,
        CompatibleAt q q' (Nat.lcm q.degree q'.degree) a a' hn hn'

/-- Two relative projective quadruples are equivalent when they are compatible at the product of
their positive degrees. -/
def Equivalent (q q' : RelativeProjQuadruple 𝒜 T) : Prop :=
  CompatibleAt q q' (q.degree * q'.degree) q'.degree q.degree
    (Nat.mul_comm q.degree q'.degree) rfl

/-- Two relative projective quadruples are compatible at some positive common multiple when both
degrees divide a positive degree at which their restricted maps are compatible. -/
def SomeCommonMultipleCompatible (q q' : RelativeProjQuadruple 𝒜 T) : Prop :=
  ∃ n a a', 0 < n ∧
    ∃ hn : n = a * q.degree,
      ∃ hn' : n = a' * q'.degree,
        CompatibleAt q q' n a a' hn hn'

/-- Compatibility at the least common multiple is equivalent to compatibility at the product of
the two positive degrees. -/
theorem compatibleAtLcm_iff_equivalent (q q' : RelativeProjQuadruple 𝒜 T) :
    CompatibleAtLcm q q' ↔ Equivalent q q' := sorry

/-- Compatibility at the product of two positive degrees is equivalent to compatibility at some
positive common multiple. -/
theorem equivalent_iff_someCommonMultipleCompatible
    (q q' : RelativeProjQuadruple 𝒜 T) :
    Equivalent q q' ↔ SomeCommonMultipleCompatible q q' := sorry

/-- Least-common-multiple compatibility, product-degree equivalence, and compatibility at some
positive common multiple are equivalent. -/
theorem equivalent_tfae (q q' : RelativeProjQuadruple 𝒜 T) :
    List.TFAE [
      CompatibleAtLcm q q',
      Equivalent q q',
      SomeCommonMultipleCompatible q q'
    ] := sorry

end AlgebraicGeometry.RelativeProjQuadruple
