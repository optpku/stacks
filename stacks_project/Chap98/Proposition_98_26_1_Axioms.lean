/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue
public import stacks_project.Chap03.Lemma_3_9_4_Size
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal
public import stacks_project.Chap98.Lemma_98_27_6_Solution
public import stacks_project.Chap98.Lemma_98_27_13_TangentSpace

/-!
# Artin axioms on the locally Noetherian étale site

Axioms [-1], [3], and [4] for Type-valued functors on
`(locallyNoetherian S).FullSubcategory`, matching the set-valued package of
Section 98.26.
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

/-- Artin axiom [-1] on the locally Noetherian site: the values of `F` on
spectra of finite-type fields over `S` are bounded by the Stacks size of some
scheme over `S`, after lifting that size to universe `u + 1`. -/
def boundedOnFiniteTypeFields {S : Scheme.{u}}
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ U : Over S, ∀ (k : Type u) [Field k] (f : Spec (CommRingCat.of k) ⟶ S)
    [LocallyOfFiniteType f],
      Cardinal.mk (F.obj (op (asLocallyNoetherian (Over.mk f)))) ≤
        Cardinal.lift.{u + 1} U.left.size

/-- Axiom [-1] unfolds to a comparison of `F.obj` cardinalities against the
lift of `Scheme.size`. -/
theorem boundedOnFiniteTypeFields_iff {S : Scheme.{u}}
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) :
    boundedOnFiniteTypeFields F ↔
      ∃ U : Over S, ∀ (k : Type u) [Field k]
        (f : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType f],
          Cardinal.mk (F.obj (op (asLocallyNoetherian (Over.mk f)))) ≤
            Cardinal.lift.{u + 1} U.left.size :=
  sorry

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

/-- Axiom [3]: every tangent space `TF_{k, x0}` of a Type-valued functor on
locally Noetherian schemes over a locally Noetherian base is finite-dimensional
over the finite-type field `k`. -/
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

/-- Axiom [3] supplies finite-dimensionality of `TF_{k, x0}` at every finite-type
field point. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S]
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

/-- Axiom [3] is equivalent to finite-dimensionality of every tangent space
`TF_{k, x0}`. -/
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

/-- Axiom [4]: every formal object of a Type-valued functor on locally
Noetherian schemes over a locally Noetherian base is effective. -/
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

/-- Axiom [4] supplies a value on `Spec(R)` restricting to any compatible
truncation system. -/
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

/-- Axiom [4] is equivalent to effectiveness of compatible `evalAt` systems on
truncations of complete local algebras. -/
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
