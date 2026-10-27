/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Spectrum
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.FieldPoints
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.GroupAction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Action

/-!
# The generic point of the affine-line translation quotient

The fppf quotient sheaf of the integer translation action, its generic-point morphism, and
its self-pullback comparison are recorded here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open IsLocalRing
open AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient
open AlgebraicGeometry.FieldExtension

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

/-- The fppf sheaf quotient of the integer translation action. -/
def sheafOfPoints (k : Type u) [Field k] [CharZero k] :
    Sheaf (Scheme.fppfTopology.over (AffineLineQuotient.base k)) (Type (u + 1)) :=
  (ofAut (action k)).quotientSheaf (Scheme.fppfTopology.over (AffineLineQuotient.base k))

/-- The canonical quotient atlas from the affine line. -/
def atlas (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.obj
        (AffineLineQuotient.cover k) ⟶ sheafOfPoints k :=
  (ofAut (action k)).quotientMap (Scheme.fppfTopology.over (AffineLineQuotient.base k))

/-- The quotient sheaf has representable diagonal. -/
theorem representableDiagonal_sheafOfPoints (k : Type u) [Field k] [CharZero k] :
    uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj) :=
  (quotientSheaf_spec_ofAut (action k)).1

/-- The quotient atlas is representable and étale. -/
theorem atlas_etale (k : Type u) [Field k] [CharZero k] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom :=
  (quotientSheaf_spec_ofAut (action k)).2.1

/-- The quotient atlas is étale-locally surjective. -/
instance atlas_locallySurjective (k : Type u) [Field k] [CharZero k] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (AffineLineQuotient.base k))
      (atlas k).hom :=
  (quotientSheaf_spec_ofAut (action k)).2.2

/-- The residue field at the generic point of the affine line. -/
abbrev genericResidueField (k : Type u) [Field k] [CharZero k] : Type u :=
  ResidueField ((AffineLineQuotient.cover k).left.presheaf.stalk
    (genericPoint (AffineLineQuotient.cover k).left))

/-- The structure morphism of the generic residue-field spectrum to the base. -/
def genericStructure (k : Type u) [Field k] [CharZero k] :
    Spec (CommRingCat.of (genericResidueField k)) ⟶ AffineLineQuotient.base k :=
  (AffineLineQuotient.cover k).left.fromSpecResidueField
      (genericPoint (AffineLineQuotient.cover k).left) ≫ (AffineLineQuotient.cover k).hom

/-- The algebra structure induced on the generic residue field by the structure morphism. -/
instance instAlgebra_genericResidueField (k : Type u) [Field k] [CharZero k] :
    Algebra k (genericResidueField k) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (genericStructure k).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (genericResidueField k))).hom).hom.toAlgebra

/-- The generic residue-field spectrum as an object over the base. -/
abbrev genericOver (k : Type u) [Field k] [CharZero k] :
    Over (AffineLineQuotient.base k) :=
  specOver (genericStructure k)

/-- The generic point of the affine line as a morphism over the base. -/
def genericToCover (k : Type u) [Field k] [CharZero k] :
    genericOver k ⟶ AffineLineQuotient.cover k :=
  Over.homMk ((AffineLineQuotient.cover k).left.fromSpecResidueField
    (genericPoint (AffineLineQuotient.cover k).left)) rfl

/-- The underlying scheme map of the generic point morphism. -/
theorem genericToCover_left (k : Type u) [Field k] [CharZero k] :
    (genericToCover k).left =
      (AffineLineQuotient.cover k).left.fromSpecResidueField
        (genericPoint (AffineLineQuotient.cover k).left) := by rfl

/-- The canonical generic-point morphism to the quotient sheaf. -/
def genericHom (k : Type u) [Field k] [CharZero k] :
    specToQuotientHom (action k) (genericStructure k) :=
  (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
      (genericToCover k) ≫ atlas k

/-- The generic point morphism lifts to the quotient atlas. -/
theorem isQuotientLift_genericToCover (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericToCover k) ≫ atlas k = genericHom k := by rfl

/-- Any monomorphic field-spectrum factorization of the generic point has an isomorphic
intervening spectrum map. -/
theorem isIso_of_mono_factor (k : Type u) [Field k] [CharZero k]
    {L : Type u} [Field L] [Algebra k L]
    (ι : specToQuotientHom (action k) (FieldExtension.specMap k L))
    (φ : genericOver k ⟶ specOver (FieldExtension.specMap k L))
    (hι : CategoryTheory.Mono ι)
    (hφ :
      (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map φ ≫ ι =
        genericHom k) :
    IsIso φ.left := by sorry

/-- The coproduct of generic residue-field spectra indexed by the acting group. -/
def genericCoproduct (k : Type u) [Field k] [CharZero k] :
    Over (AffineLineQuotient.base k) :=
  ∐ fun _ : group ↦ genericOver k

private theorem genericResidueAut_fromSpecResidueField (k : Type u) [Field k] [CharZero k]
    (g : group) :
    Spec.map (genericResidueAut k g) ≫
        (AffineLineQuotient.cover k).left.fromSpecResidueField
          (genericPoint (AffineLineQuotient.cover k).left) =
      (AffineLineQuotient.cover k).left.fromSpecResidueField
          (genericPoint (AffineLineQuotient.cover k).left) ≫ (action k g).hom.left := by
  simp [genericResidueAut, residueFieldAut, Spec.map_comp, Category.assoc]

/-- The automorphism of the generic residue field fixes the base structure map. -/
theorem genericAut_w (k : Type u) [Field k] [CharZero k] (g : group) :
    Spec.map (genericResidueAut k g) ≫ (genericOver k).hom = (genericOver k).hom := by
  change Spec.map (genericResidueAut k g) ≫
      (AffineLineQuotient.cover k).left.fromSpecResidueField
        (genericPoint (AffineLineQuotient.cover k).left) ≫ (AffineLineQuotient.cover k).hom = _
  rw [← Category.assoc, genericResidueAut_fromSpecResidueField, Category.assoc, Over.w]
  rfl

/-- The automorphism of the generic spectrum induced by a translation. -/
def genericAut (k : Type u) [Field k] [CharZero k] (g : group) :
    genericOver k ⟶ genericOver k :=
  Over.homMk (Spec.map (genericResidueAut k g)) (genericAut_w k g)

/-- The underlying scheme map of the generic-spectrum automorphism. -/
theorem genericAut_left (k : Type u) [Field k] [CharZero k] (g : group) :
    (genericAut k g).left = Spec.map (genericResidueAut k g) := by rfl

private theorem genericAut_comp_genericToCover (k : Type u) [Field k] [CharZero k]
    (g : group) :
    genericAut k g ≫ genericToCover k = genericToCover k ≫ (action k g).hom := by
  apply Over.OverMorphism.ext
  exact genericResidueAut_fromSpecResidueField k g

/-- The first projection from the indexed coproduct to the generic spectrum. -/
def genericCoproductFst (k : Type u) [Field k] [CharZero k] :
    genericCoproduct k ⟶ genericOver k :=
  Sigma.desc fun g : group ↦ genericAut k g

/-- The second projection from the indexed coproduct to the generic spectrum. -/
def genericCoproductSnd (k : Type u) [Field k] [CharZero k] :
    genericCoproduct k ⟶ genericOver k :=
  Sigma.desc fun _ : group ↦ 𝟙 (genericOver k)

set_option backward.isDefEq.respectTransparency false in
/-- Translation on the generic spectrum composes trivially with the quotient morphism. -/
theorem genericAut_comp_genericHom (k : Type u) [Field k] [CharZero k] (g : group) :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericAut k g) ≫ genericHom k = genericHom k := by
  let J := Scheme.fppfTopology.over (AffineLineQuotient.base k)
  let P := ofAut (action k)
  have hs : Sigma.ι (fun _ : group ↦ AffineLineQuotient.cover k) g ≫ P.s = 𝟙 _ := by
    simp [P, ofAut, ofHom, PreRelation.relationHom, s]
  have ht : Sigma.ι (fun _ : group ↦ AffineLineQuotient.cover k) g ≫ P.t =
      (action k g).hom := by
    simp [P, ofAut, ofHom, PreRelation.relationHom, t]
  have h :
      J.uliftYoneda.{u + 1}.map
          (Sigma.ι (fun _ : group ↦ AffineLineQuotient.cover k) g ≫ P.s) ≫ P.quotientMap J =
        J.uliftYoneda.{u + 1}.map
          (Sigma.ι (fun _ : group ↦ AffineLineQuotient.cover k) g ≫ P.t) ≫ P.quotientMap J := by
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ J.uliftYoneda.{u + 1}.map
        (Sigma.ι (fun _ : group ↦ AffineLineQuotient.cover k) g) ≫ f)
      (P.quotientMap_s_eq_t J)
  rw [hs, ht, CategoryTheory.Functor.map_id, Category.id_comp] at h
  change J.uliftYoneda.map (genericAut k g) ≫
    (J.uliftYoneda.map (genericToCover k) ≫ atlas k) = _
  rw [← CategoryTheory.Functor.map_comp_assoc, genericAut_comp_genericToCover,
    CategoryTheory.Functor.map_comp, Category.assoc]
  simpa only [J, P, atlas, genericHom, sheafOfPoints] using
    congrArg (fun f ↦ J.uliftYoneda.map (genericToCover k) ≫ f) h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The two coproduct projections become equal after composition with the generic quotient map. -/
theorem genericCoproduct_equalizes (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductFst k) ≫ genericHom k =
      (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductSnd k) ≫ genericHom k := by
  let J := Scheme.fppfTopology.over (AffineLineQuotient.base k)
  let P := ofAut (action k)
  let r : genericCoproduct k ⟶ P.left :=
    Sigma.desc fun g : group ↦
      genericToCover k ≫ Sigma.ι (fun _ : group ↦ AffineLineQuotient.cover k) g
  have ht : r ≫ P.t = genericCoproductFst k ≫ genericToCover k := by
    apply Sigma.hom_ext
    intro g
    simp [r, P, ofAut, ofHom, PreRelation.relationHom, t, genericCoproductFst,
      genericAut_comp_genericToCover]
  have hs : r ≫ P.s = genericCoproductSnd k ≫ genericToCover k := by
    apply Sigma.hom_ext
    intro g
    simp [r, P, ofAut, ofHom, PreRelation.relationHom, s, genericCoproductSnd]
  have h := congrArg (fun f ↦ J.uliftYoneda.{u + 1}.map r ≫ f)
    (P.quotientMap_s_eq_t J)
  simp only [← CategoryTheory.Functor.map_comp_assoc, hs, ht] at h
  simpa [J, P, genericHom, atlas, CategoryTheory.Functor.map_comp, Category.assoc] using h.symm

/-- The comparison map from the indexed coproduct to the generic-point self-pullback. -/
def genericPullbackIso_inv (k : Type u) [Field k] [CharZero k] :
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.obj
        (genericCoproduct k) ⟶ pullback (genericHom k) (genericHom k) :=
  pullback.lift
    ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
      (genericCoproductFst k))
    ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
      (genericCoproductSnd k))
    (genericCoproduct_equalizes k)

/-- The first projection of the comparison map is the first coproduct projection. -/
theorem genericPullbackIso_inv_fst (k : Type u) [Field k] [CharZero k] :
    genericPullbackIso_inv k ≫ pullback.fst (genericHom k) (genericHom k) =
      (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductFst k) := by
  simpa [genericPullbackIso_inv] using
    (pullback.lift_fst
      ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductFst k))
      ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductSnd k))
      (genericCoproduct_equalizes k))

/-- The second projection of the comparison map is the second coproduct projection. -/
theorem genericPullbackIso_inv_snd (k : Type u) [Field k] [CharZero k] :
    genericPullbackIso_inv k ≫ pullback.snd (genericHom k) (genericHom k) =
      (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductSnd k) := by
  simpa [genericPullbackIso_inv] using
    (pullback.lift_snd
      ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductFst k))
      ((Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map
        (genericCoproductSnd k))
      (genericCoproduct_equalizes k))

/-- The coproduct comparison map is an isomorphism of fppf sheaves. -/
instance instIsIso_genericPullbackIso_inv (k : Type u) [Field k] [CharZero k] :
    IsIso (genericPullbackIso_inv k) := by sorry

/-- The generic-point morphism is not monic. -/
theorem not_mono_genericHom (k : Type u) [Field k] [CharZero k] :
    ¬ CategoryTheory.Mono (genericHom k) := by
  intro hmono
  letI := hmono
  have h := (cancel_mono (genericHom k)).mp
    ((genericAut_comp_genericHom k (ofInt 0)).trans
      (genericAut_comp_genericHom k (ofInt 1)).symm)
  have haut : genericAut k (ofInt 0) = genericAut k (ofInt 1) :=
    (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.map_injective h
  have hres : genericResidueAut k (ofInt 0) = genericResidueAut k (ofInt 1) :=
    Spec.map_inj.mp (congrArg (fun f ↦ f.left) haut)
  have hgroup := injective_genericResidueAut k hres
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (congrArg toInt hgroup)

/-- The generic-point morphism does not factor through a monomorphism from a field spectrum. -/
theorem not_exists_mono_factor (k : Type u) [Field k] [CharZero k] :
    ¬ ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
        (ι : specToQuotientHom (action k) (FieldExtension.specMap k L))
        (hι : CategoryTheory.Mono ι)
        (φ : genericOver k ⟶ specOver (FieldExtension.specMap k L)),
        (Scheme.fppfTopology.over (AffineLineQuotient.base k)).uliftYoneda.{u + 1}.map φ ≫ ι =
          genericHom k := by
  rintro ⟨L, hL, hAlg, ι, hι, φ, hφ⟩
  letI := hL
  letI := hAlg
  letI := hι
  letI : IsIso φ.left := isIso_of_mono_factor k ι φ hι hφ
  letI : IsIso ((Over.forget (AffineLineQuotient.base k)).map φ) :=
    ‹IsIso φ.left›
  letI : IsIso φ := isIso_of_reflects_iso φ (Over.forget _)
  apply not_mono_genericHom k
  rw [← hφ]
  infer_instance

end AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation
