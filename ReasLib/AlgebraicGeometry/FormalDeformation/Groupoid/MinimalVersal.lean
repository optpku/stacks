/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.AssociatedMorphism
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Minimality
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothKernelPair
public import ReasLib.AlgebraicGeometry.FormalDeformation.ProrepresentableKernelPair
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Existence
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.MinimalVersal
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger

/-!
# Minimal versal presentations

Finite-dimensional tangent and infinitesimal-automorphism spaces give a minimal
versal formal object and a minimal smooth prorepresentable kernel-pair presentation.
-/

@[expose] public section

noncomputable section

open CategoryTheory CompleteLocalAlgCat ArtinianLocalAlgCat
open CofiberedCategoryOver.Groupoids Functor
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {G : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.Functor

/-- A deformation category with finite-dimensional tangent space admits a minimal
versal formal object in its Hom-universe lift. -/
theorem exists_isMinimalVersal [IsDeformationCategory G.p]
    [FiniteDimensional k ((fiberIsoClassFunctor G.p).obj (dualNumber Λ k))] :
    ∃ ξ : FormalObject
        (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k),
      FormalObject.IsMinimalVersal ξ := sorry

end CategoryTheory.Functor

namespace CategoryTheory.GroupoidInFunctors

/-- The kernel pair of a minimal versal formal object's associated morphism is
minimal, smooth, and prorepresentable, and its canonical quotient map is an equivalence. -/
theorem minimalPresentation_ofFormalObject
    (ξ : FormalObject
      (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k))
    [IsDeformationCategory G.p]
    [FiniteDimensional k (infinitesimalAutomorphisms G.p)]
    (hξ : FormalObject.IsMinimalVersal ξ) :
    ∃ (hs : IsSmooth (ofFormalObject ξ).s (ofFormalObject ξ).t)
      (hp : IsProrepresentable (ofFormalObject ξ)),
      IsMinimal (ofFormalObject ξ) (smooth := hs) (prorepresentable := hp) ∧
        BasedFunctor.IsEquivalence
          (quotientMap (FormalObject.associatedMorphismOver ξ)) := sorry

/-- A deformation category with finite-dimensional tangent and infinitesimal-automorphism
spaces admits a minimal versal formal object whose kernel-pair groupoid is minimal,
smooth, and prorepresentable and whose canonical quotient map is an equivalence. -/
theorem exists_minimalVersalPresentation [IsDeformationCategory G.p]
    [FiniteDimensional k ((fiberIsoClassFunctor G.p).obj (dualNumber Λ k))]
    [FiniteDimensional k (infinitesimalAutomorphisms G.p)] :
    ∃ ξ : FormalObject
        (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k),
      FormalObject.IsMinimalVersal ξ ∧
        ∃ (hs : IsSmooth (ofFormalObject ξ).s (ofFormalObject ξ).t)
          (hp : IsProrepresentable (ofFormalObject ξ)),
          IsMinimal (ofFormalObject ξ) (smooth := hs) (prorepresentable := hp) ∧
            BasedFunctor.IsEquivalence
              (quotientMap (FormalObject.associatedMorphismOver ξ)) := sorry

end CategoryTheory.GroupoidInFunctors

end
