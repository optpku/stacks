module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

/-!
# Composition of derived pullbacks on ringed spaces

The canonical underived pullback-composition isomorphism is lifted through the unbounded total
left derived functor construction.
-/

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open SheafOfModules
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical underived pullback-composition isomorphism on module sheaves over ringed
spaces. -/
noncomputable abbrev modulePullbackCompIso :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  ((pullbackComp
      (RingedSpace.Hom.toRingCatSheafHom g)
      (RingedSpace.Hom.toRingCatSheafHom f)).symm :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f)

/-- Pullback along a composite ringed-space morphism is additive. -/
noncomputable instance modulePullbackComp_additive : (pullback (f ≫ g)).Additive :=
  Functor.additive_of_iso (modulePullbackCompIso f g).symm

namespace modulePullbackDerived

/-- The canonical comparison from iterated derived pullback to derived pullback along the
composite morphism. -/
@[stacks 0D5S "derived pullback composition comparison"]
noncomputable def compComparison :
    L(g)^* ⋙ L(f)^* ⟶ L((f ≫ g))^* :=
  Functor.LeftDerived.Homotopy.Composition.comparison
    (pullback f) (pullback g) (pullback (f ≫ g)) (modulePullbackCompIso f g)

/-- Lemma 20.27.2: the canonical derived-pullback composition comparison is invertible. It is
kept as a theorem so unfinished proof debt cannot silently select inverse data. -/
@[stacks 0D5S "derived pullback composition comparison is invertible"]
theorem compComparison_isIso : IsIso (compComparison f g) := sorry

/-- Upgrade the derived-pullback composition comparison to an isomorphism from an explicit
invertibility certificate. -/
@[stacks 0D5S "derived pullback composition isomorphism"]
noncomputable def compIso (h : IsIso (compComparison f g)) :
    L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^* :=
  @asIso _ _ _ _ (compComparison f g) h

/-- The forward map of `compIso` is the canonical composition comparison. -/
@[simp, stacks 0D5S "derived pullback composition isomorphism forward map"]
theorem compIso_hom (h : IsIso (compComparison f g)) :
    (compIso f g h).hom = compComparison f g := sorry

/-- The derived-pullback composition isomorphism is independent of the supplied proof of
comparison invertibility. -/
@[stacks 0D5S "derived pullback composition proof independence"]
theorem compIso_eq (h₁ h₂ : IsIso (compComparison f g)) :
    compIso f g h₁ = compIso f g h₂ := sorry

end modulePullbackDerived

end

end AlgebraicGeometry.RingedSpace
