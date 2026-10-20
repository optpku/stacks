module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ProrepresentableKernelPair
import StacksCheckRecall

/-!
# Prorepresentable kernel-pair presentations

A morphism from a prorepresentable functor to a deformation category with
finite-dimensional infinitesimal automorphism space yields a prorepresentable
kernel-pair groupoid in functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {U : ArtinianLocalAlgCat Λ k ⥤ Type u}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (ArtinianLocalAlgCat Λ k)}

/- Lemma 90.26.3: if `F` is a deformation category, `U` is a prorepresentable functor
on `ArtinianLocalAlgCat Λ k`, and `f : U ⟶ F` is a morphism of categories cofibered in
groupoids, then the kernel-pair groupoid `ofMorphism f` constructed in Lemma 90.25.2 is
prorepresentable whenever `FiniteDimensional k (infinitesimalAutomorphisms F.p)`, i.e.
whenever `dim_k Inf(F)` is finite. -/
@[stacks 06L7] #check
  (CategoryTheory.GroupoidInFunctors.isProrepresentable_ofMorphism :
    ∀ (f : Functor.ofTypeValued.{u + 1, u, u} U ⟶ F)
      [IsDeformationCategory F.p] [Functor.IsProrepresentable U]
      [FiniteDimensional k (Functor.infinitesimalAutomorphisms F.p)],
      CategoryTheory.GroupoidInFunctors.IsProrepresentable
        (CategoryTheory.GroupoidInFunctors.ofMorphism.{u + 1, u, u} f))
