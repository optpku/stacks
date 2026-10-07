module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple
public import stacks_project.Chap75.Definition_75_28_1_ResolutionProperty

/-!
# Transfer of the resolution property along relatively ample morphisms

A morphism of algebraic spaces that admits an invertible relatively ample module
transfers the resolution property from a quasi-compact quasi-separated target to
the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `Y` is quasi-compact and quasi-separated and has the resolution property, then a
morphism `f : X ⟶ Y` of algebraic spaces admitting an invertible relatively ample
module on `X` transfers the resolution property to `X`. -/
theorem hasResolutionProperty_of_relativelyAmple {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [isInvertibleObject L] [RelativelyAmple f L]
    (hY : HasResolutionProperty Y) : HasResolutionProperty X := sorry

/-- If `Y` is quasi-compact and quasi-separated and has the resolution property, then a
morphism `f : X ⟶ Y` of algebraic spaces admitting some invertible relatively ample
module on `X` transfers the resolution property to `X`. -/
theorem hasResolutionProperty_of_exists_relativelyAmple {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (hY : HasResolutionProperty Y)
    (hL : ∃ L : X.Modules, isInvertibleObject L ∧ RelativelyAmple f L) :
    HasResolutionProperty X := sorry

end AlgebraicGeometry.AlgebraicSpace
