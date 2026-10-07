module

public import stacks_project.Chap90.Lemma_90_19_12
public import stacks_project.Chap90.Remark_90_6_4
public import stacks_project.Chap90.Remark_90_8_5_IsoClass
public import stacks_project.Chap90.Remark_90_12_5_Slice
public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of infinitesimal automorphisms and the iso-class morphism

If `p` is cofibered in groupoids and satisfies (RS), then `Inf_{x0}(F) = ⊥` if and
only if the canonical morphism `toIsoClass (sliceAt p x0)` is an equivalence of
categories cofibered in groupoids.
-/

@[expose] public section

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat
open scoped BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- The canonical based morphism `BasedFunctor.toIsoClass q` is an equivalence of
categories cofibered in groupoids if and only if `q.op` is fibered in setoids. -/
theorem toIsoClass_isEquivalence_iff_inSetoids
    {G : Type v} [Category.{w} G] (q : G ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids q.op] :
    BasedFunctor.IsEquivalence (BasedFunctor.toIsoClass q) ↔
      IsFibered.InSetoids q.op := sorry

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- The infinitesimal automorphism group of a residue-fibre object vanishes if and
only if the opposite of the residue slice `sliceAt p x0` is fibered in setoids. -/
theorem infinitesimalAutomorphismsAt_eq_bot_iff_inSetoids [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ = ⊥ ↔
      IsFibered.InSetoids (sliceAt p x0).op := sorry

/-- Lemma 90.19.13. Let `p : F ⥤ ArtinianLocalAlgCat Λ k` be a category cofibered
in groupoids over `ArtinianLocalAlgCat Λ k` satisfying (RS), and let `x0` be an
object of the residue fibre `p.Fiber (residue Λ k)`. Then
`infinitesimalAutomorphismsAt p x0 x0' φ = ⊥` if and only if the canonical
morphism `BasedFunctor.toIsoClass (sliceAt p x0)` of categories cofibered in
groupoids is an equivalence. -/
@[stacks 06K0]
theorem infinitesimalAutomorphismsAt_eq_bot_iff [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ = ⊥ ↔
      BasedFunctor.IsEquivalence (BasedFunctor.toIsoClass (sliceAt p x0)) := sorry

end CategoryTheory.Functor
