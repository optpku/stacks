/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover

open CategoryTheory AlgebraicGeometry Limits

/-!
# Stability of Zariski covering families of algebraic spaces

Zariski covering families of algebraic spaces are stable under singleton
isomorphisms, indexed composition, and base change.
-/

universe u v w

/- Lemma 73.3.2 (1)

If `X' ⟶ X` is an isomorphism of algebraic spaces over `S`, then the singleton
family `{X' ⟶ X}` is a Zariski covering of `X`. -/
@[stacks 041H] #check
  (AlgebraicGeometry.AlgebraicSpace.isZariskiCover_of_isIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X X' : AlgebraicGeometry.AlgebraicSpace S}
      (f : X' ⟶ X) [CategoryTheory.IsIso f],
      AlgebraicGeometry.AlgebraicSpace.IsZariskiCover X
        (fun _ : PUnit.{u + 1} ↦ X') (fun _ ↦ f))

/- Lemma 73.3.2 (2)

If `{Xᵢ ⟶ X}` is a Zariski covering and each `{Xᵢⱼ ⟶ Xᵢ}` is a Zariski
covering, then the composite family `{Xᵢⱼ ⟶ X}` is a Zariski covering. -/
@[stacks 041H] #check
  (AlgebraicGeometry.AlgebraicSpace.isZariskiCover_comp :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} [Small.{u} I]
      {Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      (f : ∀ i, Xᵢ i ⟶ X)
      (_ : AlgebraicGeometry.AlgebraicSpace.IsZariskiCover X Xᵢ f)
      {J : I → Type w} [∀ i, Small.{u} (J i)]
      {Xᵢⱼ : ∀ i, J i → AlgebraicGeometry.AlgebraicSpace S}
      (g : ∀ i j, Xᵢⱼ i j ⟶ Xᵢ i)
      (_ : ∀ i, AlgebraicGeometry.AlgebraicSpace.IsZariskiCover (Xᵢ i) (Xᵢⱼ i) (g i)),
      AlgebraicGeometry.AlgebraicSpace.IsZariskiCover X
        (fun p : Sigma J ↦ Xᵢⱼ p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1))

/- Lemma 73.3.2 (3)

If `{Xᵢ ⟶ X}` is a Zariski covering and `X' ⟶ X` is a morphism of algebraic
spaces, then `{X' ×_X Xᵢ ⟶ X'}` is a Zariski covering. -/
@[stacks 041H] #check
  (AlgebraicGeometry.AlgebraicSpace.isZariskiCover_pullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X X' : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} [Small.{u} I]
      {Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      (f : ∀ i, Xᵢ i ⟶ X)
      (_ : AlgebraicGeometry.AlgebraicSpace.IsZariskiCover X Xᵢ f)
      (h : X' ⟶ X),
      AlgebraicGeometry.AlgebraicSpace.IsZariskiCover X'
        (fun i ↦ pullback h (f i))
        (fun i ↦ pullback.fst h (f i)))
