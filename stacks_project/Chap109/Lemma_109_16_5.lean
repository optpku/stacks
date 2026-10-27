/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SmoothH0.Genus

/-!
# Smooth curves of a given genus

The smooth proper curve locus decomposes into clopen loci of fixed genus.
The relative-dimension-one condition is inherited from the preceding definition
of `ℳ = 𝒞urves^{smooth, h0}` and is retained in the family criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.16.5 (1): the smooth proper curve locus decomposes into
pairwise disjoint clopen genus loci, with membership characterized under every
cartesian morphism of families. -/
@[stacks 0E83] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_smoothH0OfGenus_clopen_decomposition :
  ∀ {S : Scheme.{u}} (P : Obj S)
    (h : smoothH0 S P),
    ∃ U : ℕ → (base P).left.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun g g' ↦ Disjoint (U g : Set (base P).left) (U g')) ∧
          (∀ g, IsClopen (U g : Set (base P).left)) ∧
            ∀ g, ∀ {Q : Obj S} (φ : Q ⟶ P),
              smoothH0OfGenus g S Q ↔ Set.range (baseMap φ).left ⊆ U g)

/- Lemma 109.16.5 (2): a family belongs to the smooth genus-`g` locus
precisely when it has universally trivial structure-sheaf pushforward, is
smooth of relative dimension one, and has first higher direct image of rank `g`. -/
@[stacks 0E83] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_smoothH0OfGenus_iff :
  ∀ {S : Scheme.{u}} (P : Obj S) (g : ℕ),
    smoothH0OfGenus g S P ↔
      (∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) φ))) ∧
        AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank g
            (higherDirectImageOne (hom P)))

/- Lemma 109.16.5 (3): for a proper scheme of dimension at most one over a
field, membership in the smooth genus-`g` locus is equivalent to the four
smoothness, dimension, global-functions, geometric-connectedness,
geometric-integrality, and algebraic-closure characterizations of genus `g`. -/
@[stacks 0E83] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_smoothH0OfGenus_tfae_scheme :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ),
    List.TFAE
      [smoothH0OfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
        AlgebraicGeometry.Smooth X.hom ∧
          ∃ (hdim1 : topologicalKrullDim X.left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
            SchemeOverField.genus X hdim1 hΓ = g,
        AlgebraicGeometry.Smooth X.hom ∧ GeometricallyConnected X.hom ∧
          ∃ (hdim1 : topologicalKrullDim X.left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
            SchemeOverField.genus X hdim1 hΓ = g,
        AlgebraicGeometry.Smooth X.hom ∧ GeometricallyIntegral X.hom ∧
          ∃ (hdim1 : topologicalKrullDim X.left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
            SchemeOverField.genus X hdim1 hΓ = g,
        Curve (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) ∧
          AlgebraicGeometry.Smooth
            (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).hom ∧
          ∃ (hdim1 : topologicalKrullDim
                (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap
                (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).hom)),
            SchemeOverField.genus
              (FieldExtension.Over.baseChange k (AlgebraicClosure k) X)
              hdim1 hΓ = g])

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
