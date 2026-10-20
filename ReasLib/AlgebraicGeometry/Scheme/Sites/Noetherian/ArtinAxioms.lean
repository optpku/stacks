/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Size
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.TangentSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.LocallyNoetherian

/-!
# Artin axioms on the locally Noetherian étale site

Cardinality bounds, finite-dimensional tangent spaces, and effectiveness of
formal objects for Type-valued functors on locally Noetherian schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver.Predeformation
open AlgebraicGeometry.AlgebraicSpace (ofOver homOnLocallyNoetherian)
open IsLocalRing

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Over

namespace Noetherian

/-- The values of a presheaf on finite-type fields over the base are uniformly
bounded by the universe-raised size of a scheme over the base. -/
def boundedOnFiniteTypeFields {S : Scheme.{u}}
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ U : Over S, ∀ (k : Type u) [Field k] (f : Spec (CommRingCat.of k) ⟶ S)
    [LocallyOfFiniteType f],
      Cardinal.mk (F.obj (op (asLocallyNoetherian (Over.mk f)))) ≤
        Cardinal.lift.{u + 1} U.left.size

/-- The uniform cardinal bound is equivalent to a bound by the lifted size of
one scheme over the base at every finite-type field point. -/
theorem boundedOnFiniteTypeFields_iff {S : Scheme.{u}}
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) :
    boundedOnFiniteTypeFields F ↔
      ∃ U : Over S, ∀ (k : Type u) [Field k]
        (f : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType f],
          Cardinal.mk (F.obj (op (asLocallyNoetherian (Over.mk f)))) ≤
            Cardinal.lift.{u + 1} U.left.size :=
  sorry

end Noetherian

/-- The spectrum of a Noetherian complete local algebra over `S` is locally
Noetherian. -/
instance instIsLocallyNoetherian_specCompleteLocal {S : Scheme.{u}}
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    (R : CompleteLocalAlgCat Λ k) :
    IsLocallyNoetherian
      (Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap Λ R.carrier)) ≫
          openImmersion)).left :=
  sorry

/-- Compatibility of `Spec` of the maximal-adic quotient of `R` with the
structure morphisms to `S`. -/
theorem truncationOverMap_comp {S : Scheme.{u}}
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ R.carrier)) ≫ openImmersion =
    Spec.map (CommRingCat.ofHom (algebraMap Λ (R.truncation n).carrier)) ≫
      openImmersion :=
  sorry

/-- The morphism `Spec(R ⧸ m_R ^{n+1}) ⟶ Spec(R)` over `S` induced by the
canonical quotient map of a complete local algebra. -/
def truncationOverMap {S : Scheme.{u}}
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    specOver openImmersion (R.truncation n) ⟶
      Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap Λ R.carrier)) ≫ openImmersion) :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1)))))
    (truncationOverMap_comp openImmersion R n)

/-- The underlying scheme morphism of `truncationOverMap` is `Spec` of the
maximal-adic quotient map. -/
theorem truncationOverMap_left {S : Scheme.{u}}
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (truncationOverMap openImmersion R n).left =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1)))) :=
  sorry

/-- Every tangent space of a Type-valued functor on locally Noetherian schemes
is finite-dimensional over its finite-type residue field. -/
class HasFiniteDimensionalTangentSpaces {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) : Prop where
  /-- The tangent space at every finite-type field point is finite-dimensional. -/
  finiteDimensional :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
      (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
      (h_factor :
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (x0 : F.obj (op (asLocallyNoetherian (Over.mk kToS))))
      [HasSchlessingerH2 (evalAt F openImmersion kToS h_factor x0)],
      FiniteDimensional k (tangentSpace F openImmersion kToS h_factor x0)

namespace HasFiniteDimensionalTangentSpaces

/-- A functor with finite-dimensional tangent spaces has a finite-dimensional
tangent space at each finite-type field point. -/
instance instFiniteDimensional {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    [HasFiniteDimensionalTangentSpaces F]
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : F.obj (op (asLocallyNoetherian (Over.mk kToS))))
    [HasSchlessingerH2 (evalAt F openImmersion kToS h_factor x0)] :
    FiniteDimensional k (tangentSpace F openImmersion kToS h_factor x0) :=
  sorry

end HasFiniteDimensionalTangentSpaces

/-- Having finite-dimensional tangent spaces is equivalent to
finite-dimensionality at every finite-type field point. -/
theorem hasFiniteDimensionalTangentSpaces_iff {S : Scheme.{u}}
    [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) :
    HasFiniteDimensionalTangentSpaces F ↔
      ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
        [Module.Finite Λ k]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
        (x0 : F.obj (op (asLocallyNoetherian (Over.mk kToS))))
        [HasSchlessingerH2 (evalAt F openImmersion kToS h_factor x0)],
        FiniteDimensional k (tangentSpace F openImmersion kToS h_factor x0) :=
  sorry

/-- The representable functor `Mor_S(-, V)` on locally Noetherian schemes over
`S` has finite-dimensional tangent spaces. -/
instance instHasFiniteDimensionalTangentSpaces_hom {S : Scheme.{u}}
    [IsLocallyNoetherian S] (V : Over S) [IsLocallyNoetherian V.left]
    [LocallyOfFiniteType V.hom] :
    HasFiniteDimensionalTangentSpaces (homOnLocallyNoetherian (ofOver V)) :=
  sorry

/-- Every compatible pointed system on the truncations of a complete local
algebra arises from a value of the functor on its spectrum. -/
class HasEffectiveFormalObjects {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) : Prop where
  /-- A compatible inverse system of pointed values on truncations of a
  complete local algebra is the restriction of a value on `Spec(R)`. -/
  isEffective :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
      (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
      (h_factor :
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (x0 : F.obj (op (asLocallyNoetherian (Over.mk kToS))))
      (R : CompleteLocalAlgCat Λ k)
      (ξ : ∀ n, (evalAt F openImmersion kToS h_factor x0).obj (R.truncation n)),
      (∀ n,
        (evalAt F openImmersion kToS h_factor x0).map (R.truncationMap n)
          (ξ (n + 1)) = ξ n) →
      ∃ x : F.obj (op (asLocallyNoetherian
          (Over.mk
            (Spec.map (CommRingCat.ofHom (algebraMap Λ R.carrier)) ≫
              openImmersion)))),
        ∀ n,
          F.map (op (asLocallyNoetherianMap (truncationOverMap openImmersion R n)))
            x =
            evalAt.val F openImmersion kToS h_factor x0 (ξ n)

namespace HasEffectiveFormalObjects

/-- Effectiveness supplies a value on the spectrum of a complete local algebra
restricting to a prescribed compatible pointed truncation system. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    [HasEffectiveFormalObjects F]
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : F.obj (op (asLocallyNoetherian (Over.mk kToS))))
    (R : CompleteLocalAlgCat Λ k)
    (ξ : ∀ n, (evalAt F openImmersion kToS h_factor x0).obj (R.truncation n))
    (hξ : ∀ n,
      (evalAt F openImmersion kToS h_factor x0).map (R.truncationMap n)
        (ξ (n + 1)) = ξ n) :
    ∃ x : F.obj (op (asLocallyNoetherian
        (Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap Λ R.carrier)) ≫
            openImmersion)))),
      ∀ n,
        F.map (op (asLocallyNoetherianMap (truncationOverMap openImmersion R n)))
          x =
          evalAt.val F openImmersion kToS h_factor x0 (ξ n) :=
  sorry

end HasEffectiveFormalObjects

/-- Having effective formal objects is equivalent to effectiveness of every
compatible pointed system on truncations of a complete local algebra. -/
theorem hasEffectiveFormalObjects_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) :
    HasEffectiveFormalObjects F ↔
      ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
        [Module.Finite Λ k]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
        (x0 : F.obj (op (asLocallyNoetherian (Over.mk kToS))))
        (R : CompleteLocalAlgCat Λ k)
        (ξ : ∀ n, (evalAt F openImmersion kToS h_factor x0).obj (R.truncation n)),
        (∀ n,
          (evalAt F openImmersion kToS h_factor x0).map (R.truncationMap n)
            (ξ (n + 1)) = ξ n) →
        ∃ x : F.obj (op (asLocallyNoetherian
            (Over.mk
              (Spec.map (CommRingCat.ofHom (algebraMap Λ R.carrier)) ≫
                openImmersion)))),
          ∀ n,
            F.map (op (asLocallyNoetherianMap
                (truncationOverMap openImmersion R n))) x =
              evalAt.val F openImmersion kToS h_factor x0 (ξ n) :=
  sorry

/-- The representable functor `Mor_S(-, V)` on locally Noetherian schemes over
`S` has effective formal objects. -/
instance instHasEffectiveFormalObjects_hom {S : Scheme.{u}}
    [IsLocallyNoetherian S] (V : Over S) [IsLocallyNoetherian V.left]
    [LocallyOfFiniteType V.hom] :
    HasEffectiveFormalObjects (homOnLocallyNoetherian (ofOver V)) :=
  sorry

end AlgebraicGeometry.Scheme.Over
