/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Perfect derived modules on ringed spaces

Derived perfectness on a ringed space is the specialization of the ringed-site property to the
canonical site of opens.  Complex perfectness lives in `Module/Complex/Perfect.lean`, and
open-cover criteria are kept in the `Perfect.Local` leaf.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace ModuleDerived

/-- Perfect objects of `D(𝒪_X)`, as an object property. -/
abbrev perfect : ObjectProperty (ModuleDerived X) :=
  fun K ↦ ∃ E : _root_.CochainComplex (Modules X) ℤ,
    ∃ _ : K ≅ DerivedCategory.Q.obj E, CochainComplex.IsPerfect E

/-- An object of `D(𝒪_X)` is perfect when it is represented by a perfect complex of
`𝒪_X`-modules. -/
@[stacks 08CM "(2)"]
abbrev IsPerfect (K : ModuleDerived X) : Prop :=
  perfect (X := X) K

/-- The full subcategory of perfect objects of `D(𝒪_X)`. -/
@[stacks 08CM "(2), full subcategory"]
abbrev Perfect :=
  (perfect (X := X)).FullSubcategory

namespace Perfect

/-- The canonical inclusion of perfect objects of `D(𝒪_X)`. -/
abbrev ι : Perfect (X := X) ⥤ ModuleDerived X :=
  ObjectProperty.ι _

end Perfect

/-- Perfectness of a derived `𝒪_X`-module is equivalent to the existence of a perfect
complex representative. -/
theorem isPerfect_iff_exists_representative (K : ModuleDerived X) :
    IsPerfect K ↔
      ∃ E : _root_.CochainComplex (Modules X) ℤ,
        ∃ _ : K ≅ DerivedCategory.Q.obj E, CochainComplex.IsPerfect E := sorry

/-- A perfect complex and an isomorphism from a derived object to its image exhibit a perfect
derived object. -/
theorem IsPerfect.of_iso_q_obj
    {K : ModuleDerived X} {E : _root_.CochainComplex (Modules X) ℤ}
    (hE : CochainComplex.IsPerfect E) (e : K ≅ DerivedCategory.Q.obj E) :
    IsPerfect K := sorry

/-- A perfect derived `𝒪_X`-module admits a perfect complex representative. -/
theorem IsPerfect.exists_representative
    {K : ModuleDerived X} (hK : IsPerfect K) :
    ∃ E : _root_.CochainComplex (Modules X) ℤ,
      ∃ _ : K ≅ DerivedCategory.Q.obj E, CochainComplex.IsPerfect E := sorry

/-- Perfectness of derived `𝒪_X`-modules is preserved by isomorphisms. -/
theorem IsPerfect.of_iso
    {K L : ModuleDerived X} (hK : IsPerfect K) (e : K ≅ L) :
    IsPerfect L := sorry

/-- Perfect derived modules on a ringed space are closed under isomorphisms. -/
@[stacks 08CM "isomorphism stability of perfect derived modules"]
instance perfect_isClosedUnderIsomorphisms :
    (perfect (X := X)).IsClosedUnderIsomorphisms where
  of_iso e hK := IsPerfect.of_iso hK e

/-- Every complex representing a perfect derived `𝒪_X`-module is perfect. -/
@[stacks 08CN "(2)"]
theorem IsPerfect.of_representation
    {K : ModuleDerived X} (hK : IsPerfect K)
    {E : _root_.CochainComplex (Modules X) ℤ} (e : K ≅ DerivedCategory.Q.obj E) :
    CochainComplex.IsPerfect E := sorry

end ModuleDerived

end AlgebraicGeometry.RingedSpace

namespace SheafOfModules

variable {X : AlgebraicGeometry.RingedSpace.{u}}

/-- A sheaf of `𝒪_X`-modules is perfect when its degree-zero derived realization is
perfect. -/
abbrev IsPerfect (F : AlgebraicGeometry.RingedSpace.Modules X) : Prop :=
  AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
    ((DerivedCategory.singleFunctor
      (AlgebraicGeometry.RingedSpace.Modules X) (0 : ℤ)).obj F)

end SheafOfModules
