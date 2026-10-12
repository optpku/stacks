/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

/-!
# Regular immersions of schemes

This leaf defines regularity conditions on closed immersions and immersions of
schemes through the reusable ideal-sheaf regularity API on ringed spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

section IdealSheafRegularity

variable {X : Scheme.{u}}

/-- The scheme specialization of regular ideal-sheaf regularity. -/
abbrev IsRegularIdealSheaf (I : Scheme.IdealSubobject X) : Prop :=
  RingedSpace.IsRegularIdealSheaf I

/-- The scheme specialization of Koszul-regular ideal-sheaf regularity. -/
abbrev IsKoszulRegularIdealSheaf (I : Scheme.IdealSubobject X) : Prop :=
  RingedSpace.IsKoszulRegularIdealSheaf I

/-- The scheme specialization of `H_1`-regular ideal-sheaf regularity. -/
abbrev IsH1RegularIdealSheaf (I : Scheme.IdealSubobject X) : Prop :=
  RingedSpace.IsH1RegularIdealSheaf I

/-- The scheme specialization of quasi-regular ideal-sheaf regularity. -/
abbrev IsQuasiRegularIdealSheaf (I : Scheme.IdealSubobject X) : Prop :=
  RingedSpace.IsQuasiRegularIdealSheaf I

end IdealSheafRegularity

section ClosedImmersionRegularity

variable {X Z : Scheme.{u}}

/-- A closed immersion is regular when its canonical ideal sheaf is regular. -/
class IsRegularClosedImmersion (i : Z ⟶ X) : Prop extends IsClosedImmersion i where
  /-- The canonical ideal sheaf of the closed immersion is regular. -/
  idealSheaf_isRegular : IsRegularIdealSheaf i.kernelIdealSubobject

/-- A closed immersion is Koszul-regular when its canonical ideal sheaf is Koszul-regular. -/
class IsKoszulRegularClosedImmersion (i : Z ⟶ X) : Prop extends IsClosedImmersion i where
  /-- The canonical ideal sheaf of the closed immersion is Koszul-regular. -/
  idealSheaf_isKoszulRegular : IsKoszulRegularIdealSheaf i.kernelIdealSubobject

/-- A closed immersion is `H_1`-regular when its canonical ideal sheaf is `H_1`-regular. -/
class IsH1RegularClosedImmersion (i : Z ⟶ X) : Prop extends IsClosedImmersion i where
  /-- The canonical ideal sheaf of the closed immersion is `H_1`-regular. -/
  idealSheaf_isH1Regular : IsH1RegularIdealSheaf i.kernelIdealSubobject

/-- A closed immersion is quasi-regular when its canonical ideal sheaf is quasi-regular. -/
class IsQuasiRegularClosedImmersion (i : Z ⟶ X) : Prop extends IsClosedImmersion i where
  /-- The canonical ideal sheaf of the closed immersion is quasi-regular. -/
  idealSheaf_isQuasiRegular : IsQuasiRegularIdealSheaf i.kernelIdealSubobject

/-- The closedness and regular-ideal-sheaf conditions defining a regular closed immersion. -/
theorem isRegularClosedImmersion_iff (i : Z ⟶ X) :
    IsRegularClosedImmersion i ↔
      IsClosedImmersion i ∧ IsRegularIdealSheaf i.kernelIdealSubobject := sorry

/-- The closedness and Koszul-regular-ideal-sheaf conditions defining a Koszul-regular closed
immersion. -/
theorem isKoszulRegularClosedImmersion_iff (i : Z ⟶ X) :
    IsKoszulRegularClosedImmersion i ↔
      IsClosedImmersion i ∧ IsKoszulRegularIdealSheaf i.kernelIdealSubobject := sorry

/-- The closedness and `H_1`-regular-ideal-sheaf conditions defining an `H_1`-regular closed
immersion. -/
theorem isH1RegularClosedImmersion_iff (i : Z ⟶ X) :
    IsH1RegularClosedImmersion i ↔
      IsClosedImmersion i ∧ IsH1RegularIdealSheaf i.kernelIdealSubobject := sorry

/-- The closedness and quasi-regular-ideal-sheaf conditions defining a quasi-regular closed
immersion. -/
theorem isQuasiRegularClosedImmersion_iff (i : Z ⟶ X) :
    IsQuasiRegularClosedImmersion i ↔
      IsClosedImmersion i ∧ IsQuasiRegularIdealSheaf i.kernelIdealSubobject := sorry

/-- A regular closed immersion exposes its closedness and regular ideal-sheaf conditions. -/
theorem IsRegularClosedImmersion.source_spec
    {i : Z ⟶ X} (h : IsRegularClosedImmersion i) :
    IsClosedImmersion i ∧ IsRegularIdealSheaf i.kernelIdealSubobject := sorry

/-- A Koszul-regular closed immersion exposes its closedness and Koszul-regular ideal-sheaf
conditions. -/
theorem IsKoszulRegularClosedImmersion.source_spec
    {i : Z ⟶ X} (h : IsKoszulRegularClosedImmersion i) :
    IsClosedImmersion i ∧ IsKoszulRegularIdealSheaf i.kernelIdealSubobject := sorry

/-- An `H_1`-regular closed immersion exposes its closedness and `H_1`-regular ideal-sheaf
conditions. -/
theorem IsH1RegularClosedImmersion.source_spec
    {i : Z ⟶ X} (h : IsH1RegularClosedImmersion i) :
    IsClosedImmersion i ∧ IsH1RegularIdealSheaf i.kernelIdealSubobject := sorry

/-- A quasi-regular closed immersion exposes its closedness and quasi-regular ideal-sheaf
conditions. -/
theorem IsQuasiRegularClosedImmersion.source_spec
    {i : Z ⟶ X} (h : IsQuasiRegularClosedImmersion i) :
    IsClosedImmersion i ∧ IsQuasiRegularIdealSheaf i.kernelIdealSubobject := sorry

end ClosedImmersionRegularity

section ClosedImmersionCompanions

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- A regular closed immersion supplies a regularity instance for its canonical ideal sheaf. -/
instance instIsRegularIdealSheafClosedImmersionIdealSubobject
    [h : IsRegularClosedImmersion i] :
    IsRegularIdealSheaf i.kernelIdealSubobject := sorry

/-- A Koszul-regular closed immersion supplies a Koszul-regularity instance for its canonical
ideal sheaf. -/
instance instIsKoszulRegularIdealSheafClosedImmersionIdealSubobject
    [h : IsKoszulRegularClosedImmersion i] :
    IsKoszulRegularIdealSheaf i.kernelIdealSubobject := sorry

/-- An `H_1`-regular closed immersion supplies an `H_1`-regularity instance for its canonical
ideal sheaf. -/
instance instIsH1RegularIdealSheafClosedImmersionIdealSubobject
    [h : IsH1RegularClosedImmersion i] :
    IsH1RegularIdealSheaf i.kernelIdealSubobject := sorry

/-- A quasi-regular closed immersion supplies a quasi-regularity instance for its canonical
ideal sheaf. -/
instance instIsQuasiRegularIdealSheafClosedImmersionIdealSubobject
    [h : IsQuasiRegularClosedImmersion i] :
    IsQuasiRegularIdealSheaf i.kernelIdealSubobject := sorry

end ClosedImmersionCompanions

section ImmersionRegularity

variable {X Z : Scheme.{u}}

/-- An immersion is regular when, after shrinking the target to an open subscheme, it becomes
a regular closed immersion. -/
@[stacks 063J]
class IsRegularImmersion (i : Z ⟶ X) : Prop extends IsImmersion i where
  /-- A regular immersion has a regular closed-immersion presentation over an open subscheme. -/
  exists_isRegularClosedImmersion :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, IsRegularClosedImmersion j ∧ j ≫ U.ι = i

/-- An immersion is Koszul-regular when, after shrinking the target to an open subscheme, it
becomes a Koszul-regular closed immersion. -/
@[stacks 063J]
class IsKoszulRegularImmersion (i : Z ⟶ X) : Prop extends IsImmersion i where
  /-- A Koszul-regular immersion has a Koszul-regular closed-immersion presentation over an
  open subscheme. -/
  exists_isKoszulRegularClosedImmersion :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, IsKoszulRegularClosedImmersion j ∧ j ≫ U.ι = i

/-- An immersion is `H_1`-regular when, after shrinking the target to an open subscheme, it
becomes an `H_1`-regular closed immersion. -/
@[stacks 063J]
class IsH1RegularImmersion (i : Z ⟶ X) : Prop extends IsImmersion i where
  /-- An `H_1`-regular immersion has an `H_1`-regular closed-immersion presentation over an
  open subscheme. -/
  exists_isH1RegularClosedImmersion :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, IsH1RegularClosedImmersion j ∧ j ≫ U.ι = i

/-- An immersion is quasi-regular when, after shrinking the target to an open subscheme, it
becomes a quasi-regular closed immersion. -/
@[stacks 063J]
class IsQuasiRegularImmersion (i : Z ⟶ X) : Prop extends IsImmersion i where
  /-- A quasi-regular immersion has a quasi-regular closed-immersion presentation over an open
  subscheme. -/
  exists_isQuasiRegularClosedImmersion :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, IsQuasiRegularClosedImmersion j ∧ j ≫ U.ι = i

/-- The immersion and local regular-closed-immersion conditions defining a regular immersion. -/
theorem isRegularImmersion_iff (i : Z ⟶ X) :
    IsRegularImmersion i ↔
      IsImmersion i ∧
        ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, IsRegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- The immersion and local Koszul-regular-closed-immersion conditions defining a
Koszul-regular immersion. -/
theorem isKoszulRegularImmersion_iff (i : Z ⟶ X) :
    IsKoszulRegularImmersion i ↔
      IsImmersion i ∧
        ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
          IsKoszulRegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- The immersion and local `H_1`-regular-closed-immersion conditions defining an
`H_1`-regular immersion. -/
theorem isH1RegularImmersion_iff (i : Z ⟶ X) :
    IsH1RegularImmersion i ↔
      IsImmersion i ∧
        ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
          IsH1RegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- The immersion and local quasi-regular-closed-immersion conditions defining a
quasi-regular immersion. -/
theorem isQuasiRegularImmersion_iff (i : Z ⟶ X) :
    IsQuasiRegularImmersion i ↔
      IsImmersion i ∧
        ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
          IsQuasiRegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- A regular immersion exposes its immersion condition and local regular closed presentation. -/
theorem IsRegularImmersion.source_spec
    {i : Z ⟶ X} (h : IsRegularImmersion i) :
    IsImmersion i ∧
      ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, IsRegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- A Koszul-regular immersion exposes its immersion condition and local Koszul-regular closed
presentation. -/
theorem IsKoszulRegularImmersion.source_spec
    {i : Z ⟶ X} (h : IsKoszulRegularImmersion i) :
    IsImmersion i ∧
      ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
        IsKoszulRegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- An `H_1`-regular immersion exposes its immersion condition and local `H_1`-regular closed
presentation. -/
theorem IsH1RegularImmersion.source_spec
    {i : Z ⟶ X} (h : IsH1RegularImmersion i) :
    IsImmersion i ∧
      ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
        IsH1RegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- A quasi-regular immersion exposes its immersion condition and local quasi-regular closed
presentation. -/
theorem IsQuasiRegularImmersion.source_spec
    {i : Z ⟶ X} (h : IsQuasiRegularImmersion i) :
    IsImmersion i ∧
      ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
        IsQuasiRegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

end ImmersionRegularity

section ImmersionCompanions

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- A regular immersion has a regular closed-immersion presentation over an open subscheme. -/
theorem exists_restrict_isRegularClosedImmersion [h : IsRegularImmersion i] :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme, IsRegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- A Koszul-regular immersion has a Koszul-regular closed-immersion presentation over an open
subscheme. -/
theorem exists_restrict_isKoszulRegularClosedImmersion
    [h : IsKoszulRegularImmersion i] :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
      IsKoszulRegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- An `H_1`-regular immersion has an `H_1`-regular closed-immersion presentation over an open
subscheme. -/
theorem exists_restrict_isH1RegularClosedImmersion [h : IsH1RegularImmersion i] :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
      IsH1RegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

/-- A quasi-regular immersion has a quasi-regular closed-immersion presentation over an open
subscheme. -/
theorem exists_restrict_isQuasiRegularClosedImmersion
    [h : IsQuasiRegularImmersion i] :
    ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
      IsQuasiRegularClosedImmersion j ∧ j ≫ U.ι = i := sorry

end ImmersionCompanions

end AlgebraicGeometry
