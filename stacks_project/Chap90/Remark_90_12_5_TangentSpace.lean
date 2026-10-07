module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import stacks_project.Chap90.Lemma_90_10_6
public import stacks_project.Chap90.Lemma_90_12_4
public import stacks_project.Chap90.Remark_90_12_5_Slice

/-!
# Tangent space at a residue-fibre object

The tangent space `T_x F` of a category cofibered in groupoids is the tangent
space of the residue slice `F_x`. The differential `d_x φ` is the differential
of the induced slice morphism `φ_x`.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]

/-- The tangent space of a category cofibered in groupoids `p` at a residue-fibre object
`x` is the type of isomorphism classes of the dual-number fibre of the residue slice. -/
abbrev tangentSpaceAt (x : p.Fiber (residue Λ k)) :=
  (fiberIsoClassFunctor (sliceAt p x)).obj (dualNumber Λ k)

/-- The tangent space at `x` is the dual-number value of the isomorphism-class functor of
the residue slice. -/
theorem tangentSpaceAt_def (x : p.Fiber (residue Λ k)) :
    tangentSpaceAt p x = (fiberIsoClassFunctor (sliceAt p x)).obj (dualNumber Λ k) := sorry

/-- The isomorphism class of a dual-number fibre object of the residue slice. -/
def tangentSpaceAt.mk (x : p.Fiber (residue Λ k))
    (y : (sliceAt p x).Fiber (dualNumber Λ k)) : tangentSpaceAt p x :=
  Quotient.mk'' y

/-- `tangentSpaceAt.mk` is the quotient class of a dual-number fibre object. -/
theorem tangentSpaceAt.mk_eq (x : p.Fiber (residue Λ k))
    (y : (sliceAt p x).Fiber (dualNumber Λ k)) :
    tangentSpaceAt.mk p x y = Quotient.mk'' y := sorry

/-- If `p` satisfies (S2), then the isomorphism-class functor of the residue slice satisfies
(H2). -/
instance instHasSchlessingerH2_fiberIsoClass_sliceAt [HasSchlessingerS2 p]
    (x : p.Fiber (residue Λ k)) :
    HasSchlessingerH2 (fiberIsoClassFunctor (sliceAt p x)) := sorry

/-- If `p` satisfies (S2), then `T_x F` carries the `k`-vector space structure of
Lemma 90.12.2 on the residue slice. -/
instance instModule_tangentSpaceAt [HasSchlessingerS2 p] (x : p.Fiber (residue Λ k)) :
    Module k (tangentSpaceAt p x) :=
  instModule_fiberDualTangent (sliceAt p x)

end CategoryTheory.Functor

namespace CategoryTheory.BasedFunctor

variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]

/-- The differential of a based morphism at a residue-fibre object is the map on
isomorphism classes induced by the dual-number fibre functor of `φ_x`. -/
def differentialAt (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    Functor.tangentSpaceAt p x → Functor.tangentSpaceAt q (objAt φ x) :=
  ((sliceMap φ x).fiberFunctor (dualNumber Λ k)).isoClassesMap

/-- `differentialAt φ x` is the map on isomorphism classes induced by the dual-number
fibre functor of `sliceMap φ x`. -/
theorem differentialAt_apply (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) (y : Functor.tangentSpaceAt p x) :
    differentialAt φ x y =
      ((sliceMap φ x).fiberFunctor (dualNumber Λ k)).isoClassesMap y := sorry

/-- The differential at `x` sends the class of a dual-number fibre object of the slice to
the class of its image. -/
theorem differentialAt_mk (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) (y : (Functor.sliceAt p x).Fiber (dualNumber Λ k)) :
    differentialAt φ x (Functor.tangentSpaceAt.mk p x y) =
      Functor.tangentSpaceAt.mk q (objAt φ x)
        (((sliceMap φ x).fiberFunctor (dualNumber Λ k)).obj y) := sorry

/-- If both source and target satisfy (S2), then `differentialAt φ x` is `k`-linear. -/
theorem isLinearMap_differentialAt [HasSchlessingerS2 p] [HasSchlessingerS2 q]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    IsLinearMap k (differentialAt φ x) := sorry

/-- The differential at a residue-fibre object as a bundled `k`-linear map, when both
categories cofibered in groupoids satisfy (S2). -/
def differentialLinearMapAt [HasSchlessingerS2 p] [HasSchlessingerS2 q]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    Functor.tangentSpaceAt p x →ₗ[k] Functor.tangentSpaceAt q (objAt φ x) :=
  IsLinearMap.mk' (differentialAt φ x) (isLinearMap_differentialAt φ x)

/-- The underlying function of `differentialLinearMapAt φ x` is `differentialAt φ x`. -/
theorem differentialLinearMapAt_apply [HasSchlessingerS2 p] [HasSchlessingerS2 q]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) (y : Functor.tangentSpaceAt p x) :
    differentialLinearMapAt φ x y = differentialAt φ x y := sorry

end CategoryTheory.BasedFunctor
