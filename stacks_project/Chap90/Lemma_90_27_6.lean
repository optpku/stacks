module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_10_1_DualNumber
public import stacks_project.Chap90.Definition_90_27_1
public import stacks_project.Chap90.Lemma_90_27_6_Presentation
public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Minimal versal presentations of deformation categories

A deformation category with finite-dimensional tangent space and finite-dimensional
infinitesimal automorphisms admits a minimal versal formal object. The kernel-pair
groupoid of the associated morphism is a minimal smooth prorepresentable groupoid in
functors, and the quotient morphism is an equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory CompleteLocalAlgCat ArtinianLocalAlgCat
open CofiberedCategoryOver.Groupoids
open Functor
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {G : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.Functor

/-- Lemma 90.27.6 (1): if `G` is a deformation category with finite-dimensional tangent
space, then the Hom-universe lift of `G` admits a minimal versal formal object. -/
@[stacks 06L2]
theorem exists_isMinimalVersal [IsDeformationCategory G.p]
    [AddCommGroup ((fiberIsoClassFunctor G.p).obj (dualNumber Λ k))]
    [Module k ((fiberIsoClassFunctor G.p).obj (dualNumber Λ k))]
    [FiniteDimensional k ((fiberIsoClassFunctor G.p).obj (dualNumber Λ k))] :
    ∃ ξ : FormalObject
        (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k),
      FormalObject.IsMinimalVersal ξ := sorry

end CategoryTheory.Functor

namespace CategoryTheory.GroupoidInFunctors

variable
  (ξ : FormalObject
    (ULiftHom.down ⋙ G.p : ULiftHom.{u + 1} G.total ⥤ ArtinianLocalAlgCat Λ k))

/-- The associated morphism of a versal formal object is smooth. -/
instance instIsSmooth_associatedMorphismOver [FormalObject.IsVersal ξ] :
    BasedFunctor.IsSmooth (toBasedFunctor (FormalObject.associatedMorphismOver ξ)) :=
  sorry

/-- Lemma 90.27.6 (2): the kernel-pair groupoid of the associated morphism of a
minimal versal formal object is smooth. -/
@[stacks 06L2]
instance instIsSmooth_ofFormalObject [IsDeformationCategory G.p]
    [FormalObject.IsMinimalVersal ξ] :
    IsSmooth (ofFormalObject ξ).s (ofFormalObject ξ).t := sorry

/-- Lemma 90.27.6 (3): the kernel-pair groupoid of the associated morphism is
prorepresentable whenever `Inf(G)` is finite-dimensional. -/
@[stacks 06L2]
instance instIsProrepresentable_ofFormalObject [IsDeformationCategory G.p]
    [AddCommGroup (infinitesimalAutomorphisms G.p)]
    [Module k (infinitesimalAutomorphisms G.p)]
    [FiniteDimensional k (infinitesimalAutomorphisms G.p)] :
    IsProrepresentable (ofFormalObject ξ) := sorry

/-- Lemma 90.27.6 (4): the kernel-pair groupoid of the associated morphism of a
minimal versal formal object is minimal. -/
@[stacks 06L2]
instance instIsMinimal_ofFormalObject [IsDeformationCategory G.p]
    [FormalObject.IsMinimalVersal ξ]
    [AddCommGroup (infinitesimalAutomorphisms G.p)]
    [Module k (infinitesimalAutomorphisms G.p)]
    [FiniteDimensional k (infinitesimalAutomorphisms G.p)]
    [IsSmooth (ofFormalObject ξ).s (ofFormalObject ξ).t]
    [IsProrepresentable (ofFormalObject ξ)] :
    IsMinimal (ofFormalObject ξ) := sorry

/-- The action of `[associatedMorphismOver ξ]` on a Grothendieck arrow. -/
def quotientMapOfFormalObjectHom {p q : (ofFormalObject ξ).quotient}
    (φ : p ⟶ q) :
    imageObj (FormalObject.associatedMorphismOver ξ) p.base p.fiber ⟶
      imageObj (FormalObject.associatedMorphismOver ξ) q.base q.fiber :=
  let a : PointHom (ofFormalObject ξ) q.base
      ((ofFormalObject ξ).U.map φ.base p.fiber) q.fiber :=
    φ.fiber
  imageLift (FormalObject.associatedMorphismOver ξ) φ.base p.fiber ≫
    eqToHom
      (congrArg (imageObj (FormalObject.associatedMorphismOver ξ) q.base) a.source.symm) ≫
    a.arrow.inv ≫
    eqToHom (congrArg (imageObj (FormalObject.associatedMorphismOver ξ) q.base) a.target)

/-- The canonical morphism `[U/R] ⟶ G` induced by `associatedMorphismOver ξ`. -/
def quotientMapOfFormalObject :
    BasedCategory.ofFunctor (ofFormalObject ξ).forget ⥤ᵇ G.toBasedCategory :=
  BasedFunctor.ofFunctor
    { obj p := imageObj (FormalObject.associatedMorphismOver ξ) p.base p.fiber
      map φ := quotientMapOfFormalObjectHom ξ φ
      map_id := sorry
      map_comp := sorry }
    sorry

/-- On objects, `quotientMapOfFormalObject` sends `(T, x)` to the image of `x`. -/
theorem quotientMapOfFormalObject_obj (T : ArtinianLocalAlgCat Λ k)
    (x : (ofFormalObject ξ).U.obj T) :
    (quotientMapOfFormalObject ξ).obj ((ofFormalObject ξ).quotientObj T x) =
      imageObj (FormalObject.associatedMorphismOver ξ) T x := sorry

/-- On arrows, `quotientMapOfFormalObject` is `quotientMapOfFormalObjectHom`. -/
theorem quotientMapOfFormalObject_map {p q : (ofFormalObject ξ).quotient}
    (φ : p ⟶ q) :
    (quotientMapOfFormalObject ξ).map φ = quotientMapOfFormalObjectHom ξ φ := sorry

/-- Lemma 90.27.6 (5): the quotient morphism `[U/R] ⟶ G` associated to
`associatedMorphismOver ξ` is an equivalence. -/
@[stacks 06L2]
instance instIsEquivalence_quotientMap_ofFormalObject [IsDeformationCategory G.p]
    [FormalObject.IsMinimalVersal ξ] :
    BasedFunctor.IsEquivalence (quotientMapOfFormalObject ξ) := sorry

end CategoryTheory.GroupoidInFunctors

end
