module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal.Lifting

/-!
# Versality via infinitesimal fill-in in the completion

Versality of a formal object is the infinitesimal fill-in property in the
completion along Artinian surjections, equivalently along small extensions, and
is independent of a choice of representing based functor.
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

/- Remark 90.8.10

A formal object is versal exactly when completion triangles over Artinian
surjections admit commuting lifts. It suffices to test small extensions, and
versality is independent of the choice of representing based functor. -/
@[stacks 06HS] #check (FormalObject.isVersal_iff_exists_lift :
  ∀ (ξ : FormalObject p),
    IsVersal ξ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A), Function.Surjective f.hom →
        ∀ {y x : FormalObject p} (hxy : y ⟶ x),
          (Functor.completion p).IsHomLift (inclusion.map f) hxy →
            ∀ (hξx : ξ ⟶ x), ∃ hξy : ξ ⟶ y, hξy ≫ hxy = hξx)

#check (FormalObject.isVersal_iff_exists_lift_isSmallExtension :
  ∀ (ξ : FormalObject p),
    IsVersal ξ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
        {y x : FormalObject p} (hxy : y ⟶ x),
          (Functor.completion p).IsHomLift (inclusion.map f) hxy →
            ∀ (hξx : ξ ⟶ x), ∃ hξy : ξ ⟶ y, hξy ≫ hxy = hξx)

#check (FormalObject.IsVersal.exists_lift :
  ∀ {ξ : FormalObject p} [IsVersal ξ]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    {y x : FormalObject p} (hxy : y ⟶ x)
    (hover : (Functor.completion p).IsHomLift (inclusion.map f) hxy)
    (hξx : ξ ⟶ x),
    ∃ hξy : ξ ⟶ y, hξy ≫ hxy = hξx)

#check (FormalObject.isVersal_iff_isSmooth :
  ∀ (ξ : FormalObject p)
    {φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection ξ.base) ⥤ᵇ
      BasedCategory.ofFunctor p}
    (hφ : Represents ξ φ),
    IsVersal ξ ↔ BasedFunctor.IsSmooth φ)

end FormalObject
