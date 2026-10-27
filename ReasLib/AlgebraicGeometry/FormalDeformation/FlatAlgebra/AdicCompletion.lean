/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.RingTheory.AdicCompletion.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra

/-!
# Adic completion of ring deformations

Given a Noetherian `k`-algebra `P` and an ideal `J`, a deformation
`(A, Q) ⟶ (k, P)` completes to `(A, AdicCompletion J_Q Q) ⟶ (k, AdicCompletion J P)`.
-/

@[expose] public section

open CategoryTheory Functor
open scoped BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraCat

/-- Inverse image `J_Q = f⁻¹(J)` of `J` along the structure map of a deformation of `P`. -/
def adicCompletionIdeal {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) : Ideal Q.algebra :=
  Ideal.comap f.toRingHom J

/-- The completion ideal is the comap of `J` along the underlying ring map. -/
theorem adicCompletionIdeal_eq_comap {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionIdeal J f = Ideal.comap f.toRingHom J := rfl

/-- Membership in the completion ideal is membership of the image in `J`. -/
theorem mem_adicCompletionIdeal {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) {x : Q.algebra} :
    x ∈ adicCompletionIdeal J f ↔ f.toRingHom x ∈ J := Iff.rfl

/-- The `J_Q`-adic completion of the algebra of a deformation of `P`. -/
abbrev adicCompletionAlgebra {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) : Type u :=
  AdicCompletion (adicCompletionIdeal J f) Q.algebra

/-- The completed algebra has the adic-completion carrier of the original algebra. -/
theorem adicCompletionAlgebra_def {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionAlgebra J f = AdicCompletion (adicCompletionIdeal J f) Q.algebra := rfl

/-- Completing a Noetherian deformation along `J_Q` remains flat over the Artinian base. -/
instance instModuleFlat_adicCompletionAlgebra {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    Module.Flat Q.base.carrier (adicCompletionAlgebra J f) := sorry

/-- The completed pair `(A, Q^∧)` in the category of flat algebras. -/
def adicCompletionObj {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) : FlatAlgebraCat Λ k :=
  of Q.base (adicCompletionAlgebra J f)

/-- Completing a deformation does not change the Artinian local base. -/
theorem adicCompletionObj_base {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionObj J f).base = Q.base := rfl

/-- The structure map of a deformation is adically continuous from `J_Q` to `J`. -/
def adicCompletion_adicContinuous {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    f.toRingHom.AdicContinuous (adicCompletionIdeal J f) J :=
  ⟨1, (pow_one (adicCompletionIdeal J f)).symm ▸ Ideal.map_comap_le⟩

/-- The canonical ring map `Q^∧ → P^∧` induced by a deformation of `P`. -/
def adicCompletionMap {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionAlgebra J f →+* AdicCompletion J P :=
  (adicCompletion_adicContinuous J f).completionMap

/-- The completion map extends the original structure map `Q → P`. -/
theorem adicCompletionMap_comp {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionMap J f).comp (algebraMap Q.algebra (adicCompletionAlgebra J f)) =
      (algebraMap P (AdicCompletion J P)).comp f.toRingHom :=
  (adicCompletion_adicContinuous J f).completionMap_comp

/-- The completed residue map commutes with the base algebra maps. -/
private theorem adicCompletionHom_commutes {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionMap J f).comp
        (algebraMap (adicCompletionObj J f).base.carrier (adicCompletionObj J f).algebra) =
      (algebraMap (ofResidue Λ k (AdicCompletion J P)).base.carrier
        (ofResidue Λ k (AdicCompletion J P)).algebra).comp f.baseHom.hom.toRingHom := by
  have hf : (f.toRingHom : Q.algebra →+* P).comp (algebraMap Q.base.carrier Q.algebra) =
      (algebraMap k P).comp f.baseHom.hom.toRingHom := f.commutes
  change (adicCompletionMap J f).comp
      ((algebraMap Q.algebra (adicCompletionAlgebra J f)).comp
        (algebraMap Q.base.carrier Q.algebra)) =
    ((algebraMap P (AdicCompletion J P)).comp (algebraMap k P)).comp
      f.baseHom.hom.toRingHom
  rw [← RingHom.comp_assoc, adicCompletionMap_comp J f, RingHom.comp_assoc]
  exact (congrArg
    (fun h : Q.base.carrier →+* P ↦ (algebraMap P (AdicCompletion J P)).comp h) hf).trans
      (RingHom.comp_assoc _ _ _).symm

/-- The canonical tensor lift of the completed residue map is bijective. -/
private theorem adicCompletionHom_isIsoTensor {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) :
    Function.Bijective (canonicalTensorMap
      (Q := adicCompletionObj J f) (P := ofResidue Λ k (AdicCompletion J P))
      f.baseHom (adicCompletionMap J f) (adicCompletionHom_commutes J f)) := sorry

/-- The completed residue arrow `(A, Q^∧) ⟶ (k, P^∧)`. -/
def adicCompletionHom {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    adicCompletionObj J f ⟶ ofResidue Λ k (AdicCompletion J P) :=
  Hom.of f.baseHom (adicCompletionMap J f)
    (by exact adicCompletionHom_commutes J f) (by exact adicCompletionHom_isIsoTensor J f)

/-- Completing a deformation keeps the same morphism of Artinian local bases. -/
theorem adicCompletionHom_baseHom {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    (adicCompletionHom J f).baseHom = f.baseHom := rfl

/-- A morphism of deformations is adically continuous between the inverse images of `J`. -/
def adicCompletionMap_adicContinuous {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    g.left.toRingHom.AdicContinuous (adicCompletionIdeal J ξ.hom) (adicCompletionIdeal J η.hom) :=
  ⟨1, (pow_one (adicCompletionIdeal J ξ.hom)).symm ▸
    Ideal.map_le_iff_le_comap.mpr
      ((le_of_eq (congrArg (fun h ↦ Ideal.comap h.toRingHom J) g.w).symm).trans
        (le_of_eq (Ideal.comap_comap g.left.toRingHom η.hom.toRingHom).symm))⟩

/-- The completion of a deformation morphism commutes with the base algebra maps. -/
private theorem adicCompletionMapHom_commutes {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    (adicCompletionMap_adicContinuous J g).completionMap.comp
        (algebraMap (adicCompletionObj J ξ.hom).base.carrier
          (adicCompletionObj J ξ.hom).algebra) =
      (algebraMap (adicCompletionObj J η.hom).base.carrier
        (adicCompletionObj J η.hom).algebra).comp g.left.baseHom.hom.toRingHom := by
  change (adicCompletionMap_adicContinuous J g).completionMap.comp
      ((algebraMap ξ.left.algebra (adicCompletionAlgebra J ξ.hom)).comp
        (algebraMap ξ.left.base.carrier ξ.left.algebra)) =
    ((algebraMap η.left.algebra (adicCompletionAlgebra J η.hom)).comp
      (algebraMap η.left.base.carrier η.left.algebra)).comp
      g.left.baseHom.hom.toRingHom
  rw [← RingHom.comp_assoc, (adicCompletionMap_adicContinuous J g).completionMap_comp,
    RingHom.comp_assoc, g.left.commutes, RingHom.comp_assoc]

/-- The canonical tensor lift of a completed deformation morphism is bijective. -/
private theorem adicCompletionMapHom_isIsoTensor {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    Function.Bijective (canonicalTensorMap
      (Q := adicCompletionObj J ξ.hom) (P := adicCompletionObj J η.hom)
      g.left.baseHom (adicCompletionMap_adicContinuous J g).completionMap
      (adicCompletionMapHom_commutes J g)) := sorry

/-- The completed left arrow of a morphism of deformations. -/
def adicCompletionMapHom {P : Type u} [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    adicCompletionObj J ξ.hom ⟶ adicCompletionObj J η.hom :=
  Hom.of g.left.baseHom (adicCompletionMap_adicContinuous J g).completionMap
    (by exact adicCompletionMapHom_commutes J g) (by exact adicCompletionMapHom_isIsoTensor J g)

private theorem completion_factor_eval {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | _ r =>
    simpa using AdicCompletion.Ideal.mk_eq_mk I hmn r

private theorem completion_eval_of_map_le {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} {f : R →+* S} (h : f.AdicContinuous I J)
    (hf : Ideal.map f I ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (h.completionMap x) =
      Ideal.quotientMap (J ^ n) f
        (Ideal.map_le_iff_le_comap.mp
          ((Ideal.map_pow f I n).le.trans (pow_le_pow_left' hf n)))
        (AdicCompletion.evalₐ I n x) := by
  let m := max (h.exponent * n) n
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ I m x)
  have hleft : AdicCompletion.evalₐ I (h.exponent * n) x =
      Ideal.Quotient.mk _ r := by
    rw [← completion_factor_eval I (le_max_left _ _) x, ← hr]
    rfl
  have hright : AdicCompletion.evalₐ I n x = Ideal.Quotient.mk _ r := by
    rw [← completion_factor_eval I (le_max_right _ _) x, ← hr]
    rfl
  simp [RingHom.AdicContinuous.completionMap, AdicCompletion.evalₐ_liftRingHom,
    RingHom.AdicContinuous.quotientMap, hleft, hright]

private theorem completion_comp_eq {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    {I : Ideal R} {J : Ideal S} {K : Ideal T}
    {f : R →+* S} {g : S →+* T} {c : R →+* T}
    (hf : f.AdicContinuous I J) (hg : g.AdicContinuous J K)
    (hc : c.AdicContinuous I K) (hfmap : Ideal.map f I ≤ J)
    (hgmap : Ideal.map g J ≤ K) (hcomp : g.comp f = c) :
    hg.completionMap.comp hf.completionMap = hc.completionMap := by
  have hcmap : Ideal.map c I ≤ K := by
    rw [← hcomp, ← Ideal.map_map]
    exact (Ideal.map_mono hfmap).trans hgmap
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ K n (hg.completionMap (hf.completionMap x)) = _
  rw [completion_eval_of_map_le hg hgmap, completion_eval_of_map_le hf hfmap,
    completion_eval_of_map_le hc hcmap]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr]
  simpa using congrArg (Ideal.Quotient.mk (K ^ n)) (RingHom.congr_fun hcomp r)

private theorem completion_id_eq {R : Type*} [CommRing R] (I : Ideal R)
    (h : (RingHom.id R).AdicContinuous I I) :
    h.completionMap = RingHom.id (AdicCompletion I R) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completion_eval_of_map_le h (by simp)]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr]
  simpa only [Ideal.quotientMap_mk, RingHom.id_apply] using hr

private theorem completion_hom_ext {Q P : FlatAlgebraCat Λ k} {f g : Q ⟶ P}
    (hb : f.baseHom = g.baseHom) (hr : f.toRingHom = g.toRingHom) : f = g := by
  rcases f with ⟨a, f, hcomm, hbij⟩
  rcases g with ⟨b, g, kcomm, kbij⟩
  change a = b at hb
  change f = g at hr
  cases hb
  cases hr
  rfl

private theorem completion_map_le {P : Type u} [CommRing P] [Algebra k P] (J : Ideal P)
    {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    Ideal.map g.left.toRingHom (adicCompletionIdeal J ξ.hom) ≤
      adicCompletionIdeal J η.hom :=
  Ideal.map_le_iff_le_comap.mpr
    ((le_of_eq (congrArg (fun h ↦ Ideal.comap h.toRingHom J) g.w).symm).trans
      (le_of_eq (Ideal.comap_comap g.left.toRingHom η.hom.toRingHom).symm))

/-- Completed deformation maps commute with the completed residue arrows. -/
private theorem adicCompletionMapHom_w {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {ξ η : deformationCategory Λ k P} (g : ξ ⟶ η) :
    adicCompletionMapHom J g ≫ adicCompletionHom J η.hom =
      adicCompletionHom J ξ.hom := by
  apply completion_hom_ext
  · exact congrArg (fun q : ξ.left ⟶ ofResidue Λ k P ↦ q.baseHom) g.w
  · change (adicCompletionMap J η.hom).comp
        (adicCompletionMap_adicContinuous J g).completionMap = adicCompletionMap J ξ.hom
    exact completion_comp_eq (adicCompletionMap_adicContinuous J g)
      (adicCompletion_adicContinuous J η.hom) (adicCompletion_adicContinuous J ξ.hom)
      (completion_map_le J g) Ideal.map_comap_le (congrArg Hom.toRingHom g.w)

/-- Completion preserves identity maps of deformations. -/
private theorem adicCompletionMapHom_id {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    adicCompletionMapHom J (𝟙 ξ) = 𝟙 (adicCompletionObj J ξ.hom) := by
  apply completion_hom_ext
  · rfl
  · change (adicCompletionMap_adicContinuous J (𝟙 ξ)).completionMap =
        RingHom.id (adicCompletionAlgebra J ξ.hom)
    exact completion_id_eq _ _

/-- Completion preserves composites of deformation maps. -/
private theorem adicCompletionMapHom_comp {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) {ξ η ζ : deformationCategory Λ k P}
    (g : ξ ⟶ η) (h : η ⟶ ζ) :
    adicCompletionMapHom J (g ≫ h) =
      adicCompletionMapHom J g ≫ adicCompletionMapHom J h := by
  apply completion_hom_ext
  · rfl
  · change (adicCompletionMap_adicContinuous J (g ≫ h)).completionMap =
        (adicCompletionMap_adicContinuous J h).completionMap.comp
          (adicCompletionMap_adicContinuous J g).completionMap
    exact (completion_comp_eq (adicCompletionMap_adicContinuous J g)
      (adicCompletionMap_adicContinuous J h) (adicCompletionMap_adicContinuous J (g ≫ h))
      (completion_map_le J g) (completion_map_le J h) rfl).symm

variable (Λ k) in
/-- The functor from deformations of `P` to deformations of its `J`-adic completion. -/
def adicCompletionFunctor (P : Type u) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) :
    deformationCategory Λ k P ⥤ deformationCategory Λ k (AdicCompletion J P) where
  obj ξ := Over.mk (adicCompletionHom J ξ.hom)
  map g := Over.homMk (adicCompletionMapHom J g) (by exact adicCompletionMapHom_w J g)
  map_id ξ := by
    apply Over.OverMorphism.ext
    exact adicCompletionMapHom_id J ξ
  map_comp g h := by
    apply Over.OverMorphism.ext
    exact adicCompletionMapHom_comp J g h

/-- The completed deformation has left object `(A, Q^∧)`. -/
theorem adicCompletionFunctor_obj_left {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).left = adicCompletionObj J ξ.hom := rfl

/-- The completed deformation has algebra the completion of `Q` along `J_Q`. -/
theorem adicCompletionFunctor_obj_algebra {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).left.algebra = adicCompletionAlgebra J ξ.hom := rfl

/-- The completed deformation has the canonical completed residue arrow. -/
theorem adicCompletionFunctor_obj_hom {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionFunctor Λ k P J).obj ξ).hom = adicCompletionHom J ξ.hom := rfl

variable (Λ k) in
/-- The projection from deformations of `P` to their Artinian local bases. -/
def deformationForget (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget

/-- The deformation projection sends a pair `(A, Q)` to the Artinian local algebra `A`. -/
theorem deformationForget_obj {P : Type u} [CommRing P] [Algebra k P]
    (ξ : deformationCategory Λ k P) :
    (deformationForget Λ k P).obj ξ = ξ.left.base := rfl

/-- Completing deformations commutes with projection to the Artinian local base category. -/
theorem adicCompletionFunctor_comp_forget {P : Type u} [CommRing P] [Algebra k P]
    [IsNoetherianRing P] (J : Ideal P) :
    adicCompletionFunctor Λ k P J ⋙ deformationForget Λ k (AdicCompletion J P) =
      deformationForget Λ k P := rfl

variable (Λ k) in
/-- Adic completion as a functor of categories over the Artinian local base category. -/
def adicCompletionBasedFunctor (P : Type u) [CommRing P] [Algebra k P] [IsNoetherianRing P]
    (J : Ideal P) :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (deformationForget Λ k (AdicCompletion J P)) where
  toFunctor := adicCompletionFunctor Λ k P J
  w := adicCompletionFunctor_comp_forget J

end FlatAlgebraCat
