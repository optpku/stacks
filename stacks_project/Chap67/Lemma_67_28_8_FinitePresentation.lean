/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

/-!
# Finite presentation morphisms of algebraic spaces

A morphism of algebraic spaces is of finite presentation when it is locally of
finite presentation, quasi-compact, and quasi-separated, in the sense of
Stacks Definition 67.28.1 (3).
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

/-- The source of a finite-presentation morphism with quasi-compact target is
quasi-compact. -/
theorem isQuasiCompact_of_finitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsQuasiCompact Y]
    [FinitePresentation f] : IsQuasiCompact X :=
  sorry

/-- The source of a finite-presentation morphism with quasi-separated target is
quasi-separated. -/
theorem isQuasiSeparated_of_finitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsQuasiSeparated Y]
    [FinitePresentation f] : IsQuasiSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
