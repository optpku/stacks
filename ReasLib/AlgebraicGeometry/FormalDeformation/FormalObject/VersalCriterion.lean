module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses

/-!
# Versal formal objects under Schlessinger's conditions

A formal object of a predeformation category satisfying (S1) and (S2) is versal
precisely when the induced map on dual-number fibre isomorphism classes is
surjective and every small-extension triangle in the completion admits a
ring-map fill-in on the complete local bases.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- A formal object `ξ` admits a base lift along small extensions if every
completion triangle over a small extension `B ⟶ A` of Artinian rings admits a
ring map `ξ.base ⟶ y.base` filling the base triangle. -/
def ExistsBaseLiftAlongSmallExtension [Functor.IsFibered.InGroupoids p.op]
    (ξ : FormalObject p) : Prop :=
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
    {y x : FormalObject p} (hxy : y ⟶ x),
      (Functor.completion p).IsHomLift (inclusion.map f) hxy →
        ∀ hξx : ξ ⟶ x, ∃ g : ξ.base ⟶ y.base, g ≫ hxy.base = hξx.base

/-- A formal object admits base lifts along small extensions exactly when every
completion triangle over such an extension has a commuting lift of its base map. -/
theorem existsBaseLiftAlongSmallExtension_iff [Functor.IsFibered.InGroupoids p.op]
    (ξ : FormalObject p) :
    ExistsBaseLiftAlongSmallExtension ξ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
        {y x : FormalObject p} (hxy : y ⟶ x),
          (Functor.completion p).IsHomLift (inclusion.map f) hxy →
            ∀ hξx : ξ ⟶ x, ∃ g : ξ.base ⟶ y.base, g ≫ hxy.base = hξx.base :=
  Iff.rfl

/-- A versal formal object induces a surjective map on dual-number fibre
isomorphism classes, for any representing based functor. -/
theorem IsVersal.surjective_differential {ξ : FormalObject p}
    [Functor.IsPredeformationCategory p] [IsVersal ξ]
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p)
    (hφ : Represents ξ φ) :
    Function.Surjective (φ.fiberFunctor (dualNumber Λ k)).isoClassesMap :=
  sorry

/-- A versal formal object admits a ring-map fill-in along every small extension
triangle in the completion. -/
theorem IsVersal.existsBaseLiftAlongSmallExtension
    [Functor.IsFibered.InGroupoids p.op] {ξ : FormalObject p} [IsVersal ξ] :
    ExistsBaseLiftAlongSmallExtension ξ :=
  sorry

/-- A formal object of a predeformation category satisfying (S1) and (S2) is versal
if and only if any representing based functor is surjective on dual-number fibre
isomorphism classes and every small-extension triangle in the completion admits
a commuting lift of its base map. -/
theorem isVersal_iff [Functor.IsPredeformationCategory p]
    [Functor.HasSchlessingerS1 p] [Functor.HasSchlessingerS2 p] (ξ : FormalObject p)
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p)
    (hφ : Represents ξ φ) :
    IsVersal ξ ↔
      Function.Surjective (φ.fiberFunctor (dualNumber Λ k)).isoClassesMap ∧
        ExistsBaseLiftAlongSmallExtension ξ :=
  sorry

end FormalObject
