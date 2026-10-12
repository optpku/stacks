/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_8_2_LinearMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibre products of tangent spaces

The six-term sequence of infinitesimal automorphism groups and tangent spaces of
the predeformation categories associated to a 2-fibre product of Rim-Schlessinger
categories fibred in groupoids is exact.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable {X Y Z : GroupoidsOver S}
variable (p : X ⟶ Y) (q : Z ⟶ Y)
variable [HasRimSchlessinger X] [HasRimSchlessinger Y] [HasRimSchlessinger Z]
variable (w0 : (fibreProduct p q).p.Fiber (Over.mk kToS))

/-- Lemma 98.8.2: Let `S` be a locally Noetherian scheme. Let `p : X ⟶ Y` and
`q : Z ⟶ Y` be 1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`.
Assume `X`, `Y`, `Z` satisfy (RS). Let `k` be a field of finite type over `S` and let
`w0` be an object of `W = X ×_Y Z` over `k`. Denote `x0`, `y0`, `z0` the objects of
`X`, `Y`, `Z` obtained from `w0`. Then there is a 6-term exact sequence
`0 ⟶ Inf(ℱ_{W, k, w0}) ⟶ Inf(ℱ_{X, k, x0}) × Inf(ℱ_{Z, k, z0}) ⟶ Inf(ℱ_{Y, k, y0}) ⟶
Tℱ_{W, k, w0} ⟶ Tℱ_{X, k, x0} × Tℱ_{Z, k, z0} ⟶ Tℱ_{Y, k, y0}`
of `k`-vector spaces. Source `⊕` is the module product `×`. The maps are
`infProdLinearMap`, `infDiffLinearMap`, `connectingLinearMap`,
`tangentProdLinearMap`, and `tangentDiffLinearMap`. -/
@[stacks 07X2]
theorem infTangentSequence_exact :
    Function.Injective (infProdLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (infProdLinearMap openImmersion kToS h_factor p q w0)
        (infDiffLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (infDiffLinearMap openImmersion kToS h_factor p q w0)
        (connectingLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (connectingLinearMap openImmersion kToS h_factor p q w0)
        (tangentProdLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (tangentProdLinearMap openImmersion kToS h_factor p q w0)
        (tangentDiffLinearMap openImmersion kToS h_factor p q w0) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
