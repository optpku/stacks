module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Functor

/-!
# Quotient functors and schemes over algebraic spaces

The quotient functor is imported from its mathematical owner. The category abbreviation
retains the source-facing spelling for schemes over an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}}

/-- Schemes over an algebraic space `B`. -/
abbrev SchemesOver (B : AlgebraicSpace S) := SchemeOver B

end AlgebraicGeometry.AlgebraicSpace.Quot

#check (AlgebraicGeometry.AlgebraicSpace.Quot.functor :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))
