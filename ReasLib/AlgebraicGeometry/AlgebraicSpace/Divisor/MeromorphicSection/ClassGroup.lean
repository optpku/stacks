/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.ClassGroup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Existence

/-!
# Weil divisor classes of invertible modules

Regular meromorphic sections of an invertible module on a locally Noetherian
integral algebraic space have a common Weil divisor class. Extending this
construction to ringed sites requires corresponding divisor theories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The Weil divisor class associated to a nonzero meromorphic section of an
invertible module. -/
def nonzeroMeromorphicSectionWeilDivisorClass {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) : WeilDivisorClassGroup X :=
  weilDivisorClassGroupMk X (nonzeroMeromorphicSectionWeilDivisor s hs)

/-- The class of a nonzero meromorphic section is the image of its Weil divisor
under the canonical quotient homomorphism. -/
theorem nonzeroMeromorphicSectionWeilDivisorClass_def {L : X.Modules}
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) :
    nonzeroMeromorphicSectionWeilDivisorClass s hs =
      weilDivisorClassGroupMk X (nonzeroMeromorphicSectionWeilDivisor s hs) :=
  rfl

/-- The Weil divisor class of a nonzero meromorphic section of an invertible
module is independent of the chosen regular meromorphic section. -/
theorem nonzeroMeromorphicSectionWeilDivisorClass_eq {L : X.Modules}
    [isInvertibleObject L] (s t : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t) :
    nonzeroMeromorphicSectionWeilDivisorClass s hs =
      nonzeroMeromorphicSectionWeilDivisorClass t ht :=
  sorry

/-- A class is the Weil divisor class of an invertible module if it equals the
class of every regular meromorphic section of the module. -/
def IsWeilDivisorClassOfInvertibleModule (L : X.Modules)
    [isInvertibleObject L] (c : WeilDivisorClassGroup X) : Prop :=
  ∀ (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s),
    c = nonzeroMeromorphicSectionWeilDivisorClass s hs

/-- An invertible module has a unique class equal to the divisor class of every
regular meromorphic section of the module. -/
theorem existsUnique_weilDivisorClassOfInvertibleModule (L : X.Modules)
    [isInvertibleObject L] :
    ∃! c : WeilDivisorClassGroup X, IsWeilDivisorClassOfInvertibleModule L c :=
  sorry

/-- The Weil divisor class of an invertible module is its uniquely specified
common section class, with zero as the fallback when that specification fails. -/
noncomputable def invertibleModuleWeilDivisorClass (L : X.Modules)
    [isInvertibleObject L] : WeilDivisorClassGroup X := by
  classical
  exact if h : ∃! c : WeilDivisorClassGroup X,
      IsWeilDivisorClassOfInvertibleModule L c then
    Classical.choose h.exists
  else
    0

/-- The Weil divisor class of an invertible module equals the divisor class of
every regular meromorphic section of the module. -/
theorem invertibleModuleWeilDivisorClass_spec (L : X.Modules)
    [isInvertibleObject L] :
    IsWeilDivisorClassOfInvertibleModule L (invertibleModuleWeilDivisorClass L) :=
  sorry

/-- The Weil divisor class of an invertible module equals the class of the Weil
divisor of any nonzero meromorphic section. -/
theorem invertibleModuleWeilDivisorClass_eq (L : X.Modules)
    [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) :
    invertibleModuleWeilDivisorClass L =
      nonzeroMeromorphicSectionWeilDivisorClass s hs :=
  (invertibleModuleWeilDivisorClass_spec L) s hs

end AlgebraicGeometry.AlgebraicSpace
