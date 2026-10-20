/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Absolute separation axioms for algebraic spaces

An algebraic space over a scheme is absolutely separated, locally separated,
quasi-separated, or Zariski locally quasi-separated when the corresponding
relative property holds after extending the base to the terminal scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- View an algebraic space over `S` over the terminal scheme via `terminal.from S`. -/
abbrev extendBaseTerminal {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AlgebraicSpace (⊤_ Scheme.{u}) :=
  extendBase (terminal.from S) X

/-- An algebraic space is absolutely quasi-separated when its extension to the
terminal scheme is quasi-separated over that scheme. -/
@[mk_iff]
class IsAbsolutelyQuasiSeparated {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- The space viewed over the terminal scheme is quasi-separated. -/
  isQuasiSeparated_extendBase : IsQuasiSeparated (extendBaseTerminal X)

/-- Absolute quasi-separatedness gives relative quasi-separatedness of the
extension to the terminal scheme. -/
instance instIsQuasiSeparated_extendBaseTerminal {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyQuasiSeparated X] : IsQuasiSeparated (extendBaseTerminal X) :=
  IsAbsolutelyQuasiSeparated.isQuasiSeparated_extendBase

/-- Over the terminal scheme, absolute quasi-separatedness agrees with
relative quasi-separatedness. -/
theorem isAbsolutelyQuasiSeparated_iff_isQuasiSeparated {X : AlgebraicSpace (⊤_ Scheme.{u})} :
    IsAbsolutelyQuasiSeparated X ↔ IsQuasiSeparated X := sorry

/-- A relatively quasi-separated algebraic space over the terminal scheme is
absolutely quasi-separated. -/
instance instIsAbsolutelyQuasiSeparated {X : AlgebraicSpace (⊤_ Scheme.{u})}
    [IsQuasiSeparated X] : IsAbsolutelyQuasiSeparated X := sorry

/-- Viewing over the terminal scheme is `extendBase` along `terminal.from S`. -/
theorem extendBaseTerminal_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    extendBaseTerminal X = extendBase (terminal.from S) X :=
  rfl

/-- An algebraic space is absolutely separated if it is separated after viewing over the
terminal scheme. -/
@[mk_iff]
class IsAbsolutelySeparated {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- The viewed space is separated over the terminal scheme. -/
  isSeparated_extendBase : IsSeparated (extendBaseTerminal X)

/-- An algebraic space is absolutely locally separated if it is locally separated after viewing
over the terminal scheme. This does not include quasi-separatedness. -/
@[mk_iff]
class IsAbsolutelyLocallySeparated {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- The viewed space is locally separated over the terminal scheme. -/
  isLocallySeparated_extendBase : IsLocallySeparated (extendBaseTerminal X)

/-- An algebraic space is absolutely Zariski locally quasi-separated if it is Zariski locally
quasi-separated after viewing over the terminal scheme. -/
@[mk_iff]
class IsAbsolutelyZariskiLocallyQuasiSeparated {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- The viewed space is Zariski locally quasi-separated over the terminal scheme. -/
  isZariskiLocallyQuasiSeparated_extendBase :
    IsZariskiLocallyQuasiSeparated (extendBaseTerminal X)

/-- Absolute separatedness means the diagonal of the viewed space is a closed immersion. -/
theorem IsAbsolutelySeparated.spec {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsAbsolutelySeparated X ↔
      (MorphismProperty.over (@IsClosedImmersion)).presheaf (diag (extendBaseTerminal X)) :=
  sorry

/-- Absolute local separatedness means the diagonal of the viewed space is an immersion. -/
theorem IsAbsolutelyLocallySeparated.spec {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsAbsolutelyLocallySeparated X ↔
      (MorphismProperty.over (@IsImmersion)).presheaf (diag (extendBaseTerminal X)) :=
  sorry

/-- Absolute quasi-separatedness means the diagonal of the viewed space is quasi-compact. -/
theorem IsAbsolutelyQuasiSeparated.spec {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsAbsolutelyQuasiSeparated X ↔
      (MorphismProperty.over (@QuasiCompact)).presheaf (diag (extendBaseTerminal X)) :=
  sorry

/-- Absolute Zariski-local quasi-separatedness means the viewed space admits a Zariski covering by
quasi-separated open subspaces. -/
theorem IsAbsolutelyZariskiLocallyQuasiSeparated.spec {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsAbsolutelyZariskiLocallyQuasiSeparated X ↔
      ∃ (I : Type u) (_ : Small.{u} I) (Fi : I → AlgebraicSpace (⊤_ Scheme.{u}))
        (ι : ∀ i, Fi i ⟶ extendBaseTerminal X),
        IsZariskiCover (extendBaseTerminal X) Fi ι ∧ ∀ i, IsQuasiSeparated (Fi i) :=
  sorry

/-- Over the terminal scheme, absolute separatedness agrees with relative separatedness. -/
theorem isAbsolutelySeparated_iff_isSeparated {X : AlgebraicSpace (⊤_ Scheme.{u})} :
    IsAbsolutelySeparated X ↔ IsSeparated X :=
  sorry

/-- Over the terminal scheme, absolute local separatedness agrees with relative local
separatedness. -/
theorem isAbsolutelyLocallySeparated_iff_isLocallySeparated
    {X : AlgebraicSpace (⊤_ Scheme.{u})} :
    IsAbsolutelyLocallySeparated X ↔ IsLocallySeparated X :=
  sorry

/-- Over the terminal scheme, absolute Zariski-local quasi-separatedness agrees with the relative
notion. -/
theorem IsAbsolutelyZariskiLocallyQuasiSeparated.iff_relative
    {X : AlgebraicSpace (⊤_ Scheme.{u})} :
    IsAbsolutelyZariskiLocallyQuasiSeparated X ↔ IsZariskiLocallyQuasiSeparated X :=
  sorry

/-- Absolute separatedness is the relative separatedness of the viewed space. -/
instance instIsSeparated_extendBaseTerminal {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelySeparated X] : IsSeparated (extendBaseTerminal X) :=
  IsAbsolutelySeparated.isSeparated_extendBase

/-- Absolute local separatedness is the relative local separatedness of the viewed space. -/
instance instIsLocallySeparated_extendBaseTerminal {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyLocallySeparated X] : IsLocallySeparated (extendBaseTerminal X) :=
  IsAbsolutelyLocallySeparated.isLocallySeparated_extendBase

/-- Absolute Zariski-local quasi-separatedness is the relative property of the viewed space. -/
instance instIsZariskiLocallyQuasiSeparated_extendBaseTerminal {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsAbsolutelyZariskiLocallyQuasiSeparated X] :
    IsZariskiLocallyQuasiSeparated (extendBaseTerminal X) :=
  IsAbsolutelyZariskiLocallyQuasiSeparated.isZariskiLocallyQuasiSeparated_extendBase

/-- A relatively separated algebraic space over the terminal scheme is absolutely separated. -/
instance instIsAbsolutelySeparated {X : AlgebraicSpace (⊤_ Scheme.{u})} [IsSeparated X] :
    IsAbsolutelySeparated X :=
  sorry

/-- A relatively locally separated algebraic space over the terminal scheme is absolutely
locally separated. -/
instance instIsAbsolutelyLocallySeparated {X : AlgebraicSpace (⊤_ Scheme.{u})}
    [IsLocallySeparated X] : IsAbsolutelyLocallySeparated X :=
  sorry

/-- A relatively Zariski locally quasi-separated algebraic space over the terminal scheme is
absolutely Zariski locally quasi-separated. -/
instance instIsAbsolutelyZariskiLocallyQuasiSeparated {X : AlgebraicSpace (⊤_ Scheme.{u})}
    [IsZariskiLocallyQuasiSeparated X] : IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  sorry

/-- An absolutely separated algebraic space is absolutely locally separated. -/
instance (priority := 900) instIsAbsolutelyLocallySeparated_of_isAbsolutelySeparated
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelySeparated X] :
    IsAbsolutelyLocallySeparated X :=
  sorry

/-- An absolutely separated algebraic space is absolutely quasi-separated. -/
instance (priority := 900) instIsAbsolutelyQuasiSeparated_of_isAbsolutelySeparated
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelySeparated X] :
    IsAbsolutelyQuasiSeparated X :=
  sorry

/-- An absolutely quasi-separated algebraic space is absolutely Zariski locally
quasi-separated. -/
instance (priority := 900) instIsAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelyQuasiSeparated X] :
    IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  sorry

/-- View an algebraic space over `S` over `Spec ℤ` by extending its base along
the unique morphism from `S` to `Spec ℤ`. -/
def toSpecZ {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AlgebraicSpace (Spec (.of (ULift.{u} ℤ))) :=
  extendBase (AlgebraicGeometry.specULiftZIsTerminal.from S) X

/-- Absolute quasi-separatedness agrees with relative quasi-separatedness
after extending the base to `Spec ℤ`. -/
theorem isAbsolutelyQuasiSeparated_iff_isQuasiSeparated_toSpecZ
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsAbsolutelyQuasiSeparated X ↔ IsQuasiSeparated (toSpecZ X) := sorry

/-- An absolutely quasi-separated algebraic space remains quasi-separated
when viewed over `Spec ℤ`. -/
instance instIsQuasiSeparated_toSpecZ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyQuasiSeparated X] : IsQuasiSeparated (toSpecZ X) :=
  (isAbsolutelyQuasiSeparated_iff_isQuasiSeparated_toSpecZ X).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace
