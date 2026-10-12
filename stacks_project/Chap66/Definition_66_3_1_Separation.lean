/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase

/-!
# Absolute separation axioms for algebraic spaces

An algebraic space `X` over a scheme `S` is separated, locally separated, quasi-separated, or
Zariski locally quasi-separated in the absolute sense when the corresponding relative property
holds after viewing `X` as an algebraic space over the terminal scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- View an algebraic space over `S` as an algebraic space over the terminal scheme, along
`terminal.from S`. -/
abbrev extendBaseTerminal {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AlgebraicSpace (⊤_ Scheme.{u}) :=
  extendBase (terminal.from S) X

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

/-- An algebraic space is absolutely quasi-separated if it is quasi-separated after viewing over
the terminal scheme. -/
@[mk_iff]
class IsAbsolutelyQuasiSeparated {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- The viewed space is quasi-separated over the terminal scheme. -/
  isQuasiSeparated_extendBase : IsQuasiSeparated (extendBaseTerminal X)

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

/-- Over the terminal scheme, absolute quasi-separatedness agrees with relative
quasi-separatedness. -/
theorem isAbsolutelyQuasiSeparated_iff_isQuasiSeparated {X : AlgebraicSpace (⊤_ Scheme.{u})} :
    IsAbsolutelyQuasiSeparated X ↔ IsQuasiSeparated X :=
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

/-- Absolute quasi-separatedness is the relative quasi-separatedness of the viewed space. -/
instance instIsQuasiSeparated_extendBaseTerminal {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyQuasiSeparated X] : IsQuasiSeparated (extendBaseTerminal X) :=
  IsAbsolutelyQuasiSeparated.isQuasiSeparated_extendBase

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

/-- A relatively quasi-separated algebraic space over the terminal scheme is absolutely
quasi-separated. -/
instance instIsAbsolutelyQuasiSeparated {X : AlgebraicSpace (⊤_ Scheme.{u})}
    [IsQuasiSeparated X] : IsAbsolutelyQuasiSeparated X :=
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

end AlgebraicGeometry.AlgebraicSpace
