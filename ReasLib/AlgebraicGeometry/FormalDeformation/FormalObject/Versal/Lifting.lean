module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension

/-!
# Lifting characterizations of versality

Versality of a formal object is equivalent to lifting completion triangles along
Artinian surjections, or just small extensions, and to smoothness of any
representing based functor.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [Functor.IsFibered.InGroupoids p.op]

/-- A formal object is versal exactly when every completion triangle over a
surjection of Artinian local algebras admits a commuting lift. -/
theorem isVersal_iff_exists_lift (ξ : FormalObject p) :
    IsVersal ξ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A), Function.Surjective f.hom →
        ∀ {y x : FormalObject p} (hxy : y ⟶ x),
          (Functor.completion p).IsHomLift (inclusion.map f) hxy →
            ∀ (hξx : ξ ⟶ x), ∃ hξy : ξ ⟶ y, hξy ≫ hxy = hξx :=
  sorry

/-- A formal object is versal exactly when every completion triangle over a
small extension of Artinian local algebras admits a commuting lift. -/
theorem isVersal_iff_exists_lift_isSmallExtension (ξ : FormalObject p) :
    IsVersal ξ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
        {y x : FormalObject p} (hxy : y ⟶ x),
          (Functor.completion p).IsHomLift (inclusion.map f) hxy →
            ∀ (hξx : ξ ⟶ x), ∃ hξy : ξ ⟶ y, hξy ≫ hxy = hξx :=
  sorry

/-- A versal formal object fills in every completion triangle whose vertical arrow
lies over a surjection of Artinian local algebras. -/
theorem IsVersal.exists_lift {ξ : FormalObject p} [IsVersal ξ]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    {y x : FormalObject p} (hxy : y ⟶ x)
    (hover : (Functor.completion p).IsHomLift (inclusion.map f) hxy)
    (hξx : ξ ⟶ x) :
    ∃ hξy : ξ ⟶ y, hξy ≫ hxy = hξx :=
  sorry

/-- A formal object is versal exactly when any given representing based functor
is smooth, independently of the pushforwards used to construct it. -/
theorem isVersal_iff_isSmooth (ξ : FormalObject p)
    {φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p}
    (hφ : Represents ξ φ) :
    IsVersal ξ ↔ BasedFunctor.IsSmooth φ :=
  sorry

end FormalObject
