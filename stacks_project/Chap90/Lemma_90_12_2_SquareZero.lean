module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroFunctor

/-!
# Square-zero extensions as a functor of finite `k`-modules

The assignment `V ↦ k[V]` sends a finite-dimensional vector space to its trivial
square-zero extension, and linear maps induce algebra morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- Dual-number scalar multiplication is the canonical scaling of the epsilon coefficient. -/
abbrev dualNumberSMul (scalar : k) : dualNumber Λ k ⟶ dualNumber Λ k :=
  dualNumberScaleHom Λ scalar

#check (ArtinianLocalAlgCat.squareZeroFunctor Λ k :
  FGModuleCat.{u} k ⥤ ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.dualNumberScaleHom_hom Λ k :
  ∀ scalar : k, (dualNumberSMul Λ k scalar).hom =
    (TrivSqZeroExt.map (LinearMap.lsmul k k scalar)).restrictScalars Λ)

end ArtinianLocalAlgCat
