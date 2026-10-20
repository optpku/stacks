module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth.Comparison
import StacksCheckRecall

/-!
# Smoothness via essential surjectivity of the mixed fibre comparison

Chosen pushforwards characterize smoothness through the mixed categorical pullback,
either along all surjections or only along small extensions.
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat (IsSmallExtension)
open scoped BasedFunctor

universe u v w v' w'

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/- Remark 90.8.3: Smoothness is characterized by essential surjectivity of the
comparison induced by chosen pushforwards along every surjection. -/
@[stacks 06HI] #check (CategoryTheory.BasedFunctor.isSmooth_iff_pushforwardComparison_essSurj :
  ∀    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y),
    IsSmooth φ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
        Function.Surjective f.hom →
        ∀ (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage),
          (pushforwardComparison φ χX χY f).EssSurj)

#check (CategoryTheory.BasedFunctor.isSmooth_iff_pushforwardComparison_essSurj_isSmallExtension :
  ∀    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y),
    IsSmooth φ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
        (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage),
          (pushforwardComparison φ χX χY f).EssSurj)

end CategoryTheory.BasedFunctor
