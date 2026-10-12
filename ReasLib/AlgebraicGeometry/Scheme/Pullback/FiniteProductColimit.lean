/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.RingTheory.RingHom.SurjectiveOnStalks.FiniteProductColimit

/-!
# Pullbacks of finite-product colimit spectra

This file defines the canonical map from the underlying space of a scheme pullback to the
ordinary product of the underlying spaces. It proves that this map is a homeomorphism when one
factor is the spectrum of a directed colimit of finite products of a field.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Pullback

/-- The canonical map from the underlying space of a scheme pullback to the ordinary product of
the underlying topological spaces. -/
noncomputable def toProduct {S : Scheme.{u}} (T X : Over S) :
    Scheme.forgetToTop.obj (pullback T.hom X.hom) ⟶ TopCat.of (T.left × X.left) :=
  prod.lift
      (Scheme.forgetToTop.map (pullback.fst T.hom X.hom))
      (Scheme.forgetToTop.map (pullback.snd T.hom X.hom)) ≫
    (TopCat.prodIsoProd (Scheme.forgetToTop.obj T.left)
      (Scheme.forgetToTop.obj X.left)).hom

/-- The first projection of the canonical pullback-to-product map is the pullback first
projection. -/
@[simp]
theorem toProduct_fst {S : Scheme.{u}} (T X : Over S) :
    toProduct T X ≫ TopCat.prodFst =
      Scheme.forgetToTop.map (pullback.fst T.hom X.hom) := by
  rw [toProduct, Category.assoc, TopCat.prodIsoProd_hom_fst]
  exact prod.lift_fst _ _

/-- The second projection of the canonical pullback-to-product map is the pullback second
projection. -/
@[simp]
theorem toProduct_snd {S : Scheme.{u}} (T X : Over S) :
    toProduct T X ≫ TopCat.prodSnd =
      Scheme.forgetToTop.map (pullback.snd T.hom X.hom) := by
  rw [toProduct, Category.assoc, TopCat.prodIsoProd_hom_snd]
  exact prod.lift_snd _ _

/-- If a field algebra is a directed colimit of finite function algebras, then the canonical map
from the underlying space of its spectrum after base change to the product of underlying spaces
is a homeomorphism. -/
theorem toProduct_isHomeomorph_of_finitePiColimit
    {k I : Type u} [Field k] [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommAlgCat.{u} k) (c : Cocone F) (hc : IsColimit c)
    (ι : I → Type u) [∀ i, Finite (ι i)]
    (e : ∀ i, F.obj i ≅ CommAlgCat.of k (ι i → k))
    (X : SchemeOverField k) :
    let T := OverSpec.affine (CommRingCat.ofHom (algebraMap k c.pt))
    IsHomeomorph (toProduct T X) := by
  dsimp
  let T := OverSpec.affine (CommRingCat.ofHom (algebraMap k c.pt))
  let f :
      ↥(pullback T.hom X.hom) → T.left × X.left :=
    fun x ↦ (pullback.fst T.hom X.hom x, pullback.snd T.hom X.hom x)
  let fSwap :
      ↥(pullback X.hom T.hom) → X.left × T.left :=
    fun x ↦ (pullback.fst X.hom T.hom x, pullback.snd X.hom T.hom x)
  let ePull :
      ↥(pullback T.hom X.hom) ≃ₜ ↥(pullback X.hom T.hom) :=
    Scheme.homeoOfIso (pullbackSymmetry T.hom X.hom)
  have hT : AlgebraicGeometry.SurjectiveOnStalks T.hom := by
    change AlgebraicGeometry.SurjectiveOnStalks
      (Spec.map (CommRingCat.ofHom (algebraMap k c.pt)))
    rw [AlgebraicGeometry.SurjectiveOnStalks.Spec_iff]
    exact RingHom.algebraMap_surjectiveOnStalks_of_finitePiColimit
      (k := k) F c hc ι e
  have hEmbedSwap : Topology.IsEmbedding fSwap := by
    simpa [fSwap, toProduct] using
      (AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback X.hom T.hom)
  let swap : T.left × X.left → X.left × T.left :=
    fun p ↦ (Prod.snd p, Prod.fst p)
  have hEmbed : Topology.IsEmbedding f := by
    have hSymm : Topology.IsEmbedding ePull := ePull.isEmbedding
    have hComp : Topology.IsEmbedding (swap ∘ f) := by
      have hEq : swap ∘ f = fSwap ∘ ePull := by
        funext x
        ext
        · change pullback.snd T.hom X.hom x = pullback.fst X.hom T.hom (ePull x)
          simp [ePull, ← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
        · change pullback.fst T.hom X.hom x = pullback.snd X.hom T.hom (ePull x)
          simp [ePull, ← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd]
      rw [hEq]
      exact hEmbedSwap.comp hSymm
    exact
      (Topology.IsEmbedding.of_comp_iff
        (f := f) (g := swap) (Homeomorph.prodComm T.left X.left).isEmbedding).mp hComp
  have hSurj : Function.Surjective f := by
    intro p
    obtain ⟨x, hx, hy⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := T.hom) (g := X.hom) p.1 p.2 (Subsingleton.elim _ _)
    refine ⟨x, ?_⟩
    simpa [f] using Prod.ext hx hy
  have hf : IsHomeomorph f :=
    (isHomeomorph_iff_isEmbedding_surjective).2 ⟨hEmbed, hSurj⟩
  have hToProduct : ⇑(toProduct T X) = f := by
    funext x
    apply Prod.ext
    · change (ConcreteCategory.hom (toProduct T X ≫ TopCat.prodFst)) x = (f x).1
      rw [toProduct_fst]
      rfl
    · change (ConcreteCategory.hom (toProduct T X ≫ TopCat.prodSnd)) x = (f x).2
      rw [toProduct_snd]
      rfl
  change IsHomeomorph (toProduct T X)
  rw [hToProduct]
  exact hf

end AlgebraicGeometry.Scheme.Pullback
