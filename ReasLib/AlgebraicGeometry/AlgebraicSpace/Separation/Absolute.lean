module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Absolute quasi-separatedness of algebraic spaces

Absolute quasi-separatedness is relative quasi-separatedness after extending
the base to the terminal scheme.
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

end AlgebraicGeometry.AlgebraicSpace
