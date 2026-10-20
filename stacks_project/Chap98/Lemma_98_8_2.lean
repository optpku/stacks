/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.ExactSequence

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

universe u

/- Lemma 98.8.2: Let `S` be a locally Noetherian scheme. Let `p : X ⟶ Y` and
`q : Z ⟶ Y` be 1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`.
Assume `X`, `Y`, `Z` satisfy (RS). Let `k` be a field of finite type over `S` and let
`w0` be an object of `W = X ×_Y Z` over `k`. Denote `x0`, `y0`, `z0` the objects of
`X`, `Y`, `Z` obtained from `w0`. Then there is a 6-term exact sequence
`0 ⟶ Inf(ℱ_{W, k, w0}) ⟶ Inf(ℱ_{X, k, x0}) × Inf(ℱ_{Z, k, z0}) ⟶ Inf(ℱ_{Y, k, y0}) ⟶
Tℱ_{W, k, w0} ⟶ Tℱ_{X, k, x0} × Tℱ_{Z, k, z0} ⟶ Tℱ_{Y, k, y0}`
of `k`-vector spaces. Source `⊕` is the module product `×`. The maps are
`infProdLinearMap`, `infDiffLinearMap`, `connectingLinearMap`,
`tangentProdLinearMap`, and `tangentDiffLinearMap`. -/
@[stacks 07X2] #check (AlgebraicGeometry.GroupoidsOver.Predeformation.infTangentSequence_exact :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    {X Y Z : GroupoidsOver S}
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [HasRimSchlessinger X] [HasRimSchlessinger Y] [HasRimSchlessinger Z]
    (w0 : (FiberedCategoryOver.Groupoids.p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q)).Fiber (Over.mk kToS)),
    Function.Injective (infProdLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (infProdLinearMap openImmersion kToS h_factor p q w0)
        (infDiffLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (infDiffLinearMap openImmersion kToS h_factor p q w0)
        (connectingLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (connectingLinearMap openImmersion kToS h_factor p q w0)
        (tangentProdLinearMap openImmersion kToS h_factor p q w0) ∧
      Function.Exact (tangentProdLinearMap openImmersion kToS h_factor p q w0)
        (tangentDiffLinearMap openImmersion kToS h_factor p q w0))
