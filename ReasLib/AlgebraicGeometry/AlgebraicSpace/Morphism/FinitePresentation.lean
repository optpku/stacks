module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Finite presentation morphisms of algebraic spaces

A morphism of algebraic spaces is of finite presentation when it is locally of
finite presentation, quasi-compact, and quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is of finite presentation if it is locally of
finite presentation, quasi-compact, and quasi-separated. -/
@[mk_iff]
class FinitePresentation {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends LocallyOfFinitePresentation f, QuasiCompact f, QuasiSeparated f

namespace FinitePresentation

/-- The identity morphism of an algebraic space is of finite presentation. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : FinitePresentation (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic spaces is of finite presentation. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : FinitePresentation f :=
  sorry

/-- A locally of finite presentation, quasi-compact, and quasi-separated
morphism of algebraic spaces is of finite presentation. -/
instance instOfLocallyOfFinitePresentationQuasiCompactQuasiSeparated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    FinitePresentation f where
  toLocallyOfFinitePresentation := inferInstance
  toQuasiCompact := inferInstance
  toQuasiSeparated := inferInstance

end FinitePresentation

/-- The source of a finite-presentation morphism with quasi-compact, absolutely
quasi-separated target is quasi-compact and absolutely quasi-separated. -/
theorem isQuasiCompact_and_isQuasiSeparated_of_finitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] [FinitePresentation f] :
    IsQuasiCompact X ∧ IsAbsolutelyQuasiSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
