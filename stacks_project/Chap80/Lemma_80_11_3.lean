/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Fppf

/-!
# Effective descent of algebraic spaces along fppf coverings

Countable-index fppf coverings of algebraic spaces, and descent data whose
components are of finite type, have effective algebraic-space descent data.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 80.11.3 (1): let `S` be a scheme. Let `{Xᵢ ⟶ X}_{i ∈ I}` be an fppf
covering of algebraic spaces over `S`. If `I` is countable, then any descent
datum for algebraic spaces relative to `{Xᵢ ⟶ X}` is effective. Countability of
`I` is the source size bound; a larger index type would need a size bound on
the descended spaces. Textbook descent data `(Yᵢ, φᵢⱼ)` are the components
`D.obj` and comparison maps `D.hom`. -/
@[stacks 0ADV] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.isEffective_of_countable :
    ∀ {I : Type v} [Countable I] {S : Scheme.{u}}
    {X : AlgebraicSpace S} (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
    [FppfCovering Xᵢ f] (D : DescentData Xᵢ f), D.IsEffective)

/- Lemma 80.11.3 (2): let `S` be a scheme. Let `{Xᵢ ⟶ X}_{i ∈ I}` be an fppf
covering of algebraic spaces over `S`. Any descent datum `(Yᵢ, φᵢⱼ)` relative
to `{Xᵢ ⟶ X}` with each `Yᵢ ⟶ Xᵢ` of finite type is effective. Here `Yᵢ ⟶ Xᵢ`
is the structure morphism `(D.obj i).hom`. There is no countability or
smallness hypothesis on `I`. -/
@[stacks 0ADV] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.isEffective_of_finiteType :
    ∀ {I : Type v} {S : Scheme.{u}}
    {X : AlgebraicSpace S} (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
    [FppfCovering Xᵢ f] (D : DescentData Xᵢ f)
    (h_finiteType : ∀ i, FiniteType (D.obj i).hom), D.IsEffective)
