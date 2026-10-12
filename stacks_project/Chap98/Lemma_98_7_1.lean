/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_7_1_Functor
public import stacks_project.Chap98.Lemma_98_7_1_Residue
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of field for predeformation categories

Stacks tag 07WX: a finite residue-field extension induces a canonical functor of
categories cofibered in groupoids from the reindexing `(ℱ_{𝒳, k, x₀})_{l/k}` to
`ℱ_{𝒳, l, x_{l,0}}`. If `𝒳` satisfies (RS), this functor is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (k l : Type u) [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))

/-- Lemma 98.7.1 (1). Let `S` be a locally Noetherian scheme, let `𝒳` be a category fibred
in groupoids over `(Sch/S)_{fppf}`, let `k` be a field of finite type over `S`, let `l/k`
be a finite extension, and let `x0` be an object of `𝒳` over `Spec(k)`. Writing `x_{l,0}`
for the restriction of `x0` to `Spec(l)`, there is a canonical functor
`(ℱ_{𝒳, k, x0})_{l/k} ⟶ ℱ_{𝒳, l, x_{l,0}}` of categories cofibered in groupoids over
`C_{Λ, l}`. -/
@[stacks 07WX]
def changeOfFieldFunctor :
    residueChangeBundled k l openImmersion kToS h_factor X x0 ⟶
      bundled openImmersion (lToS k l kToS) (lToS_factor k l openImmersion kToS) X
        (restrictResidue k l kToS X x0) :=
  changeOfFieldBundled k l openImmersion kToS h_factor X x0

/-- Forgetting `changeOfFieldFunctor` to based functors recovers `changeOfField`. -/
theorem changeOfFieldFunctor_toBasedFunctor :
    CofiberedCategoryOver.Groupoids.toBasedFunctor
        (changeOfFieldFunctor k l openImmersion kToS h_factor X x0) =
      changeOfField k l openImmersion kToS h_factor X x0 :=
  sorry

/-- Lemma 98.7.1 (2). If `𝒳` satisfies (RS), then the canonical change-of-field functor is
an equivalence of categories cofibered in groupoids over `C_{Λ, l}`. -/
@[stacks 07WX]
theorem changeOfField_isEquivalence [HasRimSchlessinger X] :
    BasedFunctor.IsEquivalence
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (changeOfFieldFunctor k l openImmersion kToS h_factor X x0)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
