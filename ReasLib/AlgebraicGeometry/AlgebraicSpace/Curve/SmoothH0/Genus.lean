/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SmoothH0
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Curve
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over.Proper

/-!
# Genus loci of smooth curve families

Smooth curve families with universally trivial structure-sheaf pushforward
and one-dimensional fibres decompose into clopen loci of fixed genus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of smooth families of curves with universally trivial
`𝒪_S ⟶ f_* 𝒪_X`, fibres of dimension `1`, and `R¹ f_* 𝒪_X` finite locally
free of rank `g`, corresponding to the open-and-closed substack
`𝒞urves^{smooth, h0}_g`. -/
def smoothH0OfGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    smoothH0 S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- Membership in `smoothH0OfGenus g` means the family lies in
`smoothH0` and `R¹ f_* 𝒪_X` is finite locally free of rank `g`. -/
theorem smoothH0OfGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    smoothH0OfGenus g S P ↔
      smoothH0 S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) := Iff.rfl

/-- Membership in `smoothH0OfGenus g` is membership in `smoothH0` together
with membership in `ofGenus g`. -/
theorem smoothH0OfGenus_iff_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    smoothH0OfGenus g S P ↔ smoothH0 S P ∧ ofGenus g S P := by
  constructor
  · intro h
    exact ⟨h.1, smoothH0_le_h0Dim1 P h.1, h.2⟩
  · rintro ⟨hs, hg⟩
    exact ⟨hs, hg.2⟩

/-- Membership in `smoothH0OfGenus g` implies membership in `smoothH0`. -/
theorem smoothH0OfGenus_le_smoothH0 (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    smoothH0OfGenus g S P → smoothH0 S P := fun h ↦ h.1

/-- Membership in `smoothH0OfGenus g` implies membership in `ofGenus g`. -/
theorem smoothH0OfGenus_le_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    smoothH0OfGenus g S P → ofGenus g S P :=
  fun h ↦ ((smoothH0OfGenus_iff_ofGenus g P).mp h).2

/-- A smooth family of curves over a nonempty base with universally trivial
structure-sheaf pushforward has at most one genus. -/
theorem eq_of_mem_smoothH0OfGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hbase : Nonempty (base P).left)
    (hg : smoothH0OfGenus g S P) (hg' : smoothH0OfGenus g' S P) : g = g' :=
  eq_of_mem_ofGenus hbase
    (smoothH0OfGenus_le_ofGenus g P hg) (smoothH0OfGenus_le_ofGenus g' P hg')

/-- The `smoothH0OfGenus` property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smoothH0OfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (smoothH0OfGenus g S).IsClosedUnderIsomorphisms where
  of_iso e h := (smoothH0OfGenus_iff_ofGenus g _).mpr
    ⟨(smoothH0 S).prop_of_iso e h.1,
      (ofGenus g S).prop_of_iso e (smoothH0OfGenus_le_ofGenus g _ h)⟩


/-- Every smooth curve family with universally trivial structure-sheaf
pushforward and one-dimensional fibres admits a pairwise disjoint clopen cover
of its base by fixed-genus loci, representing membership under every cartesian
morphism of families. -/
theorem exists_smoothH0OfGenus_clopen_decomposition {S : Scheme.{u}} (P : Obj S)
    (h : smoothH0 S P) :
    ∃ U : ℕ → (base P).left.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun g g' ↦ Disjoint (U g : Set (base P).left) (U g')) ∧
          (∀ g, IsClopen (U g : Set (base P).left)) ∧
            ∀ g, ∀ {Q : Obj S} (φ : Q ⟶ P),
              smoothH0OfGenus g S Q ↔ Set.range (baseMap φ).left ⊆ U g := by
  obtain ⟨U, hU, hdisj, hclopen, hmem⟩ :=
    exists_ofGenus_clopen_decomposition P (smoothH0_le_h0Dim1 P h)
  obtain ⟨V, hV⟩ := exists_smoothH0_open P
  have hVall (x : (base P).left) : x ∈ V :=
    (hV (𝟙 P)).mp h ⟨x, rfl⟩
  refine ⟨U, hU, hdisj, hclopen, ?_⟩
  intro g Q φ
  constructor
  · intro hQ
    exact (hmem g φ).mp (smoothH0OfGenus_le_ofGenus g Q hQ)
  · intro hrange
    exact (smoothH0OfGenus_iff_ofGenus g Q).mpr
      ⟨(hV φ).mpr (fun x _ ↦ hVall x), (hmem g φ).mpr hrange⟩

/-- A curve family belongs to the smooth genus-`g` locus precisely when its
canonical structure-sheaf pushforward unit is an isomorphism after every base
change, it is smooth of relative dimension one, and its first structure-sheaf
higher direct image is finite locally free of rank `g`. -/
theorem classifying_factorsThrough_smoothH0OfGenus_iff
    {S : Scheme.{u}} (P : Obj S) (g : ℕ) :
    smoothH0OfGenus g S P ↔
      (∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) φ))) ∧
        AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank g
            (higherDirectImageOne (hom P)) := by
  simp only [smoothH0OfGenus_iff, smoothH0_iff, and_assoc]

/-- For a proper scheme of dimension at most one over a field, membership in
the smooth genus-`g` locus is equivalent to smoothness in dimension one with
bijective canonical global-sections map and genus `g`, with geometric
connectedness and genus `g`, or with geometric integrality and genus `g`, and
to being a smooth curve of genus `g` after algebraic-closure base change. -/
theorem classifying_factorsThrough_smoothH0OfGenus_tfae_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) :
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
              hdim1 hΓ = g] := by
  let Y := FieldExtension.Over.baseChange k (AlgebraicClosure k) X
  have hgenus (hdim1 : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (hYdim : topologicalKrullDim Y.left = 1)
      (hYΓ : Function.Bijective (Scheme.Hom.globalSectionsMap Y.hom)) :
      SchemeOverField.genus Y hYdim hYΓ = SchemeOverField.genus X hdim1 hΓ :=
    SchemeOverField.baseChange_genus_eq (K := AlgebraicClosure k) X hdim1 hΓ
  have ht := classifying_factorsThrough_smoothH0_tfae_scheme X hdim
  have hfunctions :
      smoothH0 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) := ht.out 0 1
  have hconnected :
      (AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) ↔
      AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
        GeometricallyConnected X.hom := ht.out 1 2
  have hintegral :
      (AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) ↔
      AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
        GeometricallyIntegral X.hom := ht.out 1 3
  have hclosure :
      (AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) ↔
      Curve Y ∧ AlgebraicGeometry.Smooth Y.hom := ht.out 1 4
  refine List.tfae_cons_cons.mpr ⟨?_, ?_⟩
  · constructor
    · intro h
      obtain ⟨hdim1, hΓ, hg⟩ := (ofGenus_iff_scheme X hdim g).mp
        (smoothH0OfGenus_le_ofGenus g _ h)
      exact ⟨(hfunctions.mp h.1).1, hdim1, hΓ, hg⟩
    · rintro ⟨hs, hdim1, hΓ, hg⟩
      exact (smoothH0OfGenus_iff_ofGenus g _).mpr
        ⟨hfunctions.mpr ⟨hs, hdim1, hΓ⟩,
          (ofGenus_iff_scheme X hdim g).mpr ⟨hdim1, hΓ, hg⟩⟩
  · refine List.tfae_cons_cons.mpr ⟨?_, ?_⟩
    · constructor
      · rintro ⟨hs, hdim1, hΓ, hg⟩
        exact ⟨hs, (hconnected.mp ⟨hs, hdim1, hΓ⟩).2.2, hdim1, hΓ, hg⟩
      · rintro ⟨hs, _, hdim1, hΓ, hg⟩
        exact ⟨hs, hdim1, hΓ, hg⟩
    · refine List.tfae_cons_cons.mpr ⟨?_, ?_⟩
      · constructor
        · rintro ⟨hs, _, hdim1, hΓ, hg⟩
          exact ⟨hs, (hintegral.mp ⟨hs, hdim1, hΓ⟩).2.2, hdim1, hΓ, hg⟩
        · rintro ⟨hs, _, hdim1, hΓ, hg⟩
          exact ⟨hs, (hconnected.mp ⟨hs, hdim1, hΓ⟩).2.2, hdim1, hΓ, hg⟩
      · refine List.tfae_cons_cons.mpr ⟨?_, List.tfae_singleton _⟩
        constructor
        · rintro ⟨hs, _, hdim1, hΓ, hg⟩
          obtain ⟨hcurve, hsY⟩ := hclosure.mp ⟨hs, hdim1, hΓ⟩
          have hYdim : topologicalKrullDim Y.left = 1 :=
            SchemeOverField.baseChange_topologicalKrullDim_eq_one
              (K := AlgebraicClosure k) X hdim1 hΓ
          have hYΓ : Function.Bijective (Scheme.Hom.globalSectionsMap Y.hom) :=
            SchemeOverField.baseChange_globalSectionsMap_bijective
              (K := AlgebraicClosure k) X hdim1 hΓ
          exact ⟨hcurve, hsY, hYdim, hYΓ, (hgenus hdim1 hΓ hYdim hYΓ).trans hg⟩
        · rintro ⟨hcurve, hsY, hYdim, hYΓ, hg⟩
          obtain ⟨hs, hdim1, hΓ⟩ := hclosure.mpr ⟨hcurve, hsY⟩
          exact ⟨hs, (hintegral.mp ⟨hs, hdim1, hΓ⟩).2.2, hdim1, hΓ,
            (hgenus hdim1 hΓ hYdim hYΓ).symm.trans hg⟩

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
