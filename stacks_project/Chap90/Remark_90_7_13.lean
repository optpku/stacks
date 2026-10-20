module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom.ChangeBase
import StacksCheckRecall

@[expose] public section

open CategoryTheory FormalObject
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}
variable [hp : Functor.IsFibered.InGroupoids p.op]

/- Remark 90.7.13: a morphism `a : ξ ⟶ η` of formal objects of a category `F`
cofibered in groupoids over `C_Λ`, with base map `f = a.base` in `Ĉ_Λ`, induces a
2-cell `underline ξ ∘ f ⟶ underline η` in the 2-category of categories over `C_Λ`.
Components at `α : S ⟶ A` are the unique CFG comparisons
`β_{m,*} ξ_m ⟶ α_{m,*} η_m` over `id A`. Lean truncation index `n` uses the
maximal-ideal power `n + 1`, so the source's least vanishing positive exponent
corresponds to Lean stage `nilpotencyIndex A`. -/
@[stacks 06SL] #check (FormalObject.toRestrictedHom₂Hom :
  ∀ {ξ η : FormalObject p} (a : ξ ⟶ η),
    CompleteLocalAlgCat.restrictedCoyonedaBasedMap a.base ⋙
        (FormalObject.toRestrictedHom ξ.base).obj ⟨ξ, rfl⟩ ⟶
      (FormalObject.toRestrictedHom η.base).obj ⟨η, rfl⟩)
