/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.Counterexample.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Approximation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Deformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Module
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

/-!
# Failure of openness of versality for an annihilator covering condition

The covering subfibration satisfies the stack, limit, deformation, finiteness,
and approximation conditions, while its versal locus need not be open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation
open Functor.Fiber
open scoped AlgebraicGeometry Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.ArtinVersalityCounterexample

variable (k : Type u) [Field k]

/-- The covering groupoid fibration is a stack in groupoids for the étale topology. -/
instance instIsStackInGroupoids_etale :
    IsStack.InGroupoids (Scheme.etaleTopology.over (baseScheme k)) (groupoids k).p :=
  sorry

/-- The covering groupoid fibration preserves directed inverse limits of affine schemes. -/
instance instLimitPreserving :
    AlgebraicGeometry.Groupoids.LimitPreserving (groupoids k) :=
  sorry

/-- The covering groupoid fibration satisfies the Rim–Schlessinger condition. -/
instance instHasRimSchlessinger :
    HasRimSchlessinger (groupoids k) :=
  sorry

/-- The morphism `Spec(k') ⟶ Spec(Λ)` associated to a finite type `Λ`-field `k'`. -/
def fieldToBase (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k'] :
    Spec (CommRingCat.of k') ⟶ baseScheme k :=
  (specOver (𝟙 (baseScheme k)) (ArtinianLocalAlgCat.residue (coordRing k) k')).hom

/-- The identity chart `Spec(Λ) ⟶ Spec(Λ)` factors the residue morphism of `k'`. -/
theorem fieldToBase_factor (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k'] :
    Spec.map (CommRingCat.ofHom (algebraMap (coordRing k) k')) ≫ 𝟙 (baseScheme k) =
      fieldToBase k k' :=
  rfl

/-- A finite type `Λ`-algebra structure on a field yields a locally finite type
morphism `Spec(k') ⟶ Spec(Λ)`. -/
instance instLocallyOfFiniteType_fieldToBase (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k'] :
    LocallyOfFiniteType (fieldToBase k k') :=
  sorry

/-- The predeformation functor `ℱ_{X, k', x0}` relative to the identity chart of
`Spec(Λ)`. -/
abbrev predeformationAt (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :=
  predeformationFunctor (groupoids k) (𝟙 (baseScheme k)) (fieldToBase k k')
    (fieldToBase_factor k k') x0

/-- The tangent space of `ℱ_{X, k', x0}` on the identity chart. -/
abbrev tangentSpaceAt (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :=
  (fiberIsoClassFunctor (predeformationAt k k' x0)).obj
    (ArtinianLocalAlgCat.dualNumber (coordRing k) k')

/-- The tangent space at every finite type field object is finite dimensional over its residue field. -/
@[instance]
theorem finiteDimensional_tangent (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))) :
    FiniteDimensional k' (tangentSpaceAt k k' x0) :=
  sorry

/-- Infinitesimal automorphisms at every finite type field object form a finite-dimensional vector space. -/
@[instance]
theorem finiteDimensional_infAut (k' : Type u) [Field k']
    [Algebra (coordRing k) k'] [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (ξ0 : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k'))
    (ξ0' : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))
    (φ : fiberInclusion.obj ξ0 ⟶ fiberInclusion.obj ξ0')
    [hφ : (predeformationAt k k' x0).IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') φ] :
    FiniteDimensional k'
      (infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ) :=
  sorry

/-- Restriction to maximal-adic thickenings is an equivalence from complete local objects to formal objects. -/
instance instApproximationIsEquivalence :
    (approximation (groupoids k)).IsEquivalence :=
  sorry

/-- The spectrum of the quotient by the first generator satisfies the affine covering condition. -/
theorem testOver_isCovered : IsCovered k (testOver k) :=
  sorry

/-- The quotient spectrum, equipped with its covering property, is an object of the covering subfibration. -/
def identityObject : (groupoids k).total :=
  ⟨testOver k, testOver_isCovered k⟩

/-- The quotient-spectrum object projects to the morphism induced by the quotient map. -/
theorem identityObject_over :
    (groupoids k).p.obj (identityObject k) = Over.mk (testToBase k) :=
  rfl

/-- The identity object over the quotient by the first generator is versal precisely at the origin among finite type points. -/
theorem exists_versal_only_at_origin :
    IsFiniteTypePoint (origin k) ∧
      IsVersalAt (testToBase k) (identityObject k) (identityObject_over k) (origin k) ∧
        ∀ u : testScheme k, IsFiniteTypePoint u → u ≠ origin k →
          ¬ IsVersalAt (testToBase k) (identityObject k) (identityObject_over k) u :=
  sorry

/-- The covering groupoid fibration fails openness of versality. -/
theorem not_opennessOfVersality :
    ¬ AlgebraicGeometry.GroupoidsOver.OpennessOfVersality (groupoids k) :=
  sorry

end AlgebraicGeometry.ArtinVersalityCounterexample
