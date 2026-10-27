/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient.Relation

/-!
# The coordinate-axes quotient algebraic space

This module records the fppf sheaf quotient `X = U / R` of the coordinate axes by the
étale relation given by the diagonal and punctured axis-swap graph, together with the descended
morphism `X ⟶ 𝔸¹_k` induced by `(x, y) ↦ x + y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.Sheaf (isUniversalHomeomorphism)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient

/-- The fppf sheaf `X = U / R`, obtained by sheafifying the universe-raised quotient presheaf. -/
def sheafOfPoints (k : Type u) [Field k] :
    Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)) :=
  (preRelation k).quotientSheaf (Scheme.fppfTopology.over (base k))


/-- The atlas `U ⟶ X` as a morphism of fppf sheaves, given by the canonical quotient map. -/
def atlas (k : Type u) [Field k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) ⟶ sheafOfPoints k :=
  (preRelation k).quotientMap (Scheme.fppfTopology.over (base k))


/-- The fppf quotient sheaf `X = U / R` is an algebraic space over `Spec k`: it has a
representable étale locally-surjective atlas from `U` and a representable diagonal. -/
theorem sheafOfPoints_spec (k : Type u) [Field k] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom ∧
        uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj) := sorry

/-- The diagonal of `X = U / R` is quasi-compact relative to `uliftYoneda`, so `X` is
quasi-separated. -/
theorem quasiCompact_diag_sheafOfPoints (k : Type u) [Field k] :
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag (sheafOfPoints k).obj) := sorry

/-- The affine line `𝔸¹_k` as a scheme over `Spec k`. -/
def affineLine (k : Type u) [Field k] : Over (base k) :=
  Over.mk ((𝔸(ULift.{u} (Fin 1); base k) ↘ base k))

/-- The underlying scheme of `affineLine` is affine 1-space over `k`. -/
theorem affineLine_left (k : Type u) [Field k] :
    (affineLine k).left = 𝔸(ULift.{u} (Fin 1); base k) := rfl

/-- The structure morphism of `affineLine` is the canonical map `𝔸¹_k ⟶ Spec k`. -/
theorem affineLine_hom (k : Type u) [Field k] :
    (affineLine k).hom = (𝔸(ULift.{u} (Fin 1); base k) ↘ base k) := rfl

/-- The unique coordinate function on `𝔸¹_k`. -/
def affineLineCoord (k : Type u) [Field k] : Γ((affineLine k).left, ⊤) :=
  AffineSpace.coord (base k) (ULift.up (0 : Fin 1))


/-- The basic open `D(t) ⊆ 𝔸¹_k`. -/
def puncturedAffineLineOpen (k : Type u) [Field k] : (affineLine k).left.Opens :=
  (affineLine k).left.basicOpen (affineLineCoord k)


/-- The open `𝔸¹_k \ {0}` as a scheme over `Spec k`. -/
def puncturedAffineLineOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk ((puncturedAffineLineOpen k).ι ≫ (affineLine k).hom)

/-- The structure morphism of `puncturedAffineLineOver` is the open immersion followed by
the structure map of the affine line. -/
theorem puncturedAffineLineOver_hom (k : Type u) [Field k] :
    (puncturedAffineLineOver k).hom =
      (puncturedAffineLineOpen k).ι ≫ (affineLine k).hom := rfl

/-- The open immersion `𝔸¹_k \ {0} ⟶ 𝔸¹_k` as a morphism over `Spec k`. -/
def puncturedAffineLineι (k : Type u) [Field k] : puncturedAffineLineOver k ⟶ affineLine k :=
  Over.homMk (puncturedAffineLineOpen k).ι

/-- The underlying scheme map of `puncturedAffineLineι` is the open immersion of `D(t)`. -/
theorem puncturedAffineLineι_left (k : Type u) [Field k] :
    (puncturedAffineLineι k).left = (puncturedAffineLineOpen k).ι := rfl

/-- The inclusion of `𝔸¹_k \ {0}` into the affine line is an open immersion. -/
instance instIsOpenImmersion_puncturedAffineLineι (k : Type u) [Field k] :
    IsOpenImmersion (puncturedAffineLineι k).left := inferInstanceAs (IsOpenImmersion (puncturedAffineLineOpen k).ι)

/-- The origin of `𝔸¹_k`, viewed as a scheme over `Spec k`. -/
def affineLineOriginOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk (AffineSpace.homOfVector (𝟙 (base k)) (fun _ : ULift.{u} (Fin 1) ↦ 0) ≫ (affineLine k).hom)


/-- The origin morphism `Spec k ⟶ 𝔸¹_k` over `Spec k`. -/
def affineLineOriginToAffineLine (k : Type u) [Field k] :
    affineLineOriginOver k ⟶ affineLine k :=
  Over.homMk (AffineSpace.homOfVector (𝟙 (base k)) (fun _ : ULift.{u} (Fin 1) ↦ 0))

/-- The underlying scheme morphism of `affineLineOriginToAffineLine` is the zero section. -/
theorem affineLineOriginToAffineLine_left (k : Type u) [Field k] :
    (affineLineOriginToAffineLine k).left =
      AffineSpace.homOfVector (𝟙 (base k)) (fun _ : ULift.{u} (Fin 1) ↦ 0) := rfl

/-- The morphism `U ⟶ 𝔸¹_k` given by `(x, y) ↦ x + y` commutes with the structure
morphisms to `Spec k`. -/
private theorem sumOver_w (k : Type u) [Field k] :
    AffineSpace.homOfVector (cover k).hom (fun _ : ULift.{u} (Fin 1) ↦ sumSection k) ≫
        (affineLine k).hom = (cover k).hom :=
  AffineSpace.homOfVector_over _ _

/-- The morphism `U ⟶ 𝔸¹_k` sending `(x, y)` to `x + y`. -/
def sumOver (k : Type u) [Field k] : cover k ⟶ affineLine k :=
  Over.homMk
    (AffineSpace.homOfVector (cover k).hom (fun _ : ULift.{u} (Fin 1) ↦ sumSection k))
    (by exact sumOver_w k)

/-- The underlying scheme morphism of `sumOver` is `homOfVector` of the section `x + y`. -/
theorem sumOver_left (k : Type u) [Field k] :
    (sumOver k).left =
      AffineSpace.homOfVector (cover k).hom (fun _ : ULift.{u} (Fin 1) ↦ sumSection k) := rfl

/-- The sum map equalizes the two projections of the coordinate-axes relation. -/
theorem sumOver_equalizes (k : Type u) [Field k] :
    (preRelation k).t ≫ sumOver k = (preRelation k).s ≫ sumOver k := by
  have hcoord (i : ULift.{u} (Fin 2)) :
      (flip k).left.appTop (coord k i) =
        coord k (Equiv.swap (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)) i) := by
    change (Spec.map (CommRingCat.ofHom (flipRingHom k))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (coordinateRing k))).inv _) = _
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    change (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing k))).inv
      (Ideal.Quotient.mk (relationIdeal k) (flipRename k (MvPolynomial.X i))) =
        (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing k))).inv
          (Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X
            (Equiv.swap (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)) i)))
    rw [show flipRename k (MvPolynomial.X i) = MvPolynomial.X
      (Equiv.swap (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)) i) from
        MvPolynomial.rename_X _ _]
  have hflip : flip k ≫ sumOver k = sumOver k := by
    apply Over.OverMorphism.ext
    change (flip k).left ≫ AffineSpace.homOfVector (cover k).hom
      (fun _ : ULift.{u} (Fin 1) ↦ sumSection k) =
        AffineSpace.homOfVector (cover k).hom
          (fun _ : ULift.{u} (Fin 1) ↦ sumSection k)
    rw [AffineSpace.comp_homOfVector, Over.w]
    congr 1
    funext i
    simp [sumSection, hcoord, add_comm]
  apply Sigma.hom_ext
  intro i
  have hι : Sigma.ι (relationComponent k) i ≫ relationHom k = relationComponentHom k i :=
    Sigma.ι_desc (relationComponentHom k) i
  change Sigma.ι (relationComponent k) i ≫ (relationHom k ≫ prod.fst) ≫ sumOver k =
    Sigma.ι (relationComponent k) i ≫ (relationHom k ≫ prod.snd) ≫ sumOver k
  simp only [← Category.assoc, hι]
  cases i
  · change (prod.lift (𝟙 (cover k)) (𝟙 (cover k)) ≫ prod.fst) ≫ sumOver k =
      (prod.lift (𝟙 (cover k)) (𝟙 (cover k)) ≫ prod.snd) ≫ sumOver k
    rw [prod.lift_fst (𝟙 (cover k)) (𝟙 (cover k)),
      prod.lift_snd (𝟙 (cover k)) (𝟙 (cover k))]
  · change ((puncturedι k ≫ prod.lift (𝟙 (cover k)) (flip k)) ≫ prod.fst) ≫ sumOver k =
      ((puncturedι k ≫ prod.lift (𝟙 (cover k)) (flip k)) ≫ prod.snd) ≫ sumOver k
    simp only [Category.assoc, prod.lift_fst_assoc (𝟙 (cover k)) (flip k),
      prod.lift_snd_assoc (𝟙 (cover k)) (flip k), Category.id_comp]
    exact congrArg (fun f ↦ puncturedι k ≫ f) hflip.symm

/-- The descended morphism `X ⟶ 𝔸¹_k` induced by `(x, y) ↦ x + y` on the atlas. -/
def toAffineLine (k : Type u) [Field k] :
    sheafOfPoints k ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (affineLine k) :=
  (preRelation k).quotientSheafDesc (Scheme.fppfTopology.over (base k))
    (sumOver k) (sumOver_equalizes k)


/-- On the atlas, `toAffineLine` recovers the sum map `(x, y) ↦ x + y`. -/
theorem toAffineLine_comp_atlas (k : Type u) [Field k] :
    atlas k ≫ toAffineLine k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (sumOver k) := 
  (preRelation k).quotientSheafDesc_quotientMap (Scheme.fppfTopology.over (base k))
    (sumOver k) (sumOver_equalizes k)

/-- `toAffineLine` is an isomorphism after base change along `𝔸¹_k \ {0} ⟶ 𝔸¹_k`. -/
theorem isIso_over_punctured (k : Type u) [Field k] :
    IsIso
      (pullback.snd (toAffineLine k)
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
          (puncturedAffineLineι k))) :=
  sorry

/-- The morphism `X ⟶ 𝔸¹_k` is a universal homeomorphism in the sense of
the étale-atlas criterion. -/
theorem universalHomeomorphism_toAffineLine (k : Type u) [Field k] :
    isUniversalHomeomorphism (toAffineLine k) := sorry

/-- The affine line over `k` is an integral scheme. -/
instance instIsIntegral_affineLine (k : Type u) [Field k] :
    AlgebraicGeometry.IsIntegral (affineLine k).left := inferInstanceAs (AlgebraicGeometry.IsIntegral 𝔸(ULift.{u} (Fin 1); base k))


/-- The affine line over `k` is a locally Noetherian scheme. -/
instance instIsLocallyNoetherian_affineLine (k : Type u) [Field k] :
    AlgebraicGeometry.IsLocallyNoetherian (affineLine k).left :=
  isLocallyNoetherian_of_isOpenImmersion
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom


/-- The affine line over `k` is a Noetherian scheme. -/
instance instIsNoetherian_affineLine (k : Type u) [Field k] :
    AlgebraicGeometry.IsNoetherian (affineLine k).left where
  toCompactSpace := inferInstanceAs (CompactSpace 𝔸(ULift.{u} (Fin 1); base k))


/-- The top open of the affine line is nonempty. -/
instance instNonempty_top_affineLine (k : Type u) [Field k] :
    Nonempty (⊤ : (affineLine k).left.Opens) :=
  ⟨⟨genericPoint (affineLine k).left, Set.mem_univ _⟩⟩


/-- The quotient has a reduced atlas, a universal homeomorphism to an integral target,
and a quasi-compact diagonal. -/
theorem isIntegral (k : Type u) [Field k] :
    AlgebraicGeometry.IsReduced (cover k).left ∧
      Sheaf.isUniversalHomeomorphism (toAffineLine k) ∧
      AlgebraicGeometry.IsIntegral (affineLine k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) := by
  have hradical : (relationIdeal k).IsRadical := by
    apply isRadical_iff_span_singleton.mp
    intro n f hf
    have hx := (MvPolynomial.X_prime (R := k) (i := ULift.up (0 : Fin 2)))
    have hy := (MvPolynomial.X_prime (R := k) (i := ULift.up (1 : Fin 2)))
    have hxf : MvPolynomial.X (ULift.up (0 : Fin 2)) ∣ f :=
      hx.dvd_of_dvd_pow ((dvd_mul_right _ _).trans hf)
    have hyf : MvPolynomial.X (ULift.up (1 : Fin 2)) ∣ f :=
      hy.dvd_of_dvd_pow ((dvd_mul_left _ _).trans hf)
    obtain ⟨g, rfl⟩ := hxf
    have hyg : MvPolynomial.X (ULift.up (1 : Fin 2)) ∣ g :=
      (hy.dvd_mul.mp hyf).resolve_left (by simp)
    obtain ⟨h, rfl⟩ := hyg
    exact ⟨h, (mul_assoc _ _ _).symm⟩
  letI : _root_.IsReduced (coordinateRing k) :=
    (Ideal.isRadical_iff_quotient_reduced (relationIdeal k)).mp hradical
  exact ⟨inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (coordinateRing k)))),
    universalHomeomorphism_toAffineLine k, inferInstance, quasiCompact_diag_sheafOfPoints k⟩


/-- The quotient has a Noetherian atlas and a quasi-compact diagonal. -/
theorem isNoetherian (k : Type u) [Field k] :
    AlgebraicGeometry.IsNoetherian (cover k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) := by
  letI : IsNoetherianRing (coordinateRing k) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial (ULift.{u} (Fin 2)) k ⧸ relationIdeal k))
  exact ⟨inferInstanceAs (AlgebraicGeometry.IsNoetherian
    (Spec (CommRingCat.of (coordinateRing k)))), quasiCompact_diag_sheafOfPoints k⟩

end AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient
