/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine

/-!
# Integral closure of the structure sheaf in a quasi-coherent algebra

On the small étale site of an algebraic space, the integral closure of `𝒪_X` in a
quasi-coherent `𝒪_X`-algebra `A` is the sheaf whose sections over `U` are the elements of
`A(U)` that become integral after restriction along some covering family.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- A section of a quasi-coherent `𝒪_X`-algebra over an étale object is locally integral if it
becomes integral after restriction along some covering family in the small étale precoverage. -/
def IsLocallyIntegral {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) (a : sectionRing A U) : Prop :=
  ∃ R : Presieve U, R ∈ smallEtalePrecoverage X U ∧
    ∀ ⦃V : smallEtaleSite X⦄ (f : V ⟶ U), R f →
      _root_.IsIntegral Γ(V.left.left, ⊤) ((A.obj.right.obj.map f.op).hom a)

private theorem isIntegral_map {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (f : V ⟶ U)
    {a : sectionRing A U} (ha : _root_.IsIntegral Γ(U.left.left, ⊤) a) :
    _root_.IsIntegral Γ(V.left.left, ⊤) ((A.obj.right.obj.map f.op).hom a) := by
  refine _root_.IsIntegral.map_of_comp_eq
    (R := Γ(U.left.left, ⊤)) (S := sectionRing A U)
    (T := Γ(V.left.left, ⊤)) (U := sectionRing A V)
    ((commStructureSheaf X).obj.map f.op).hom (A.obj.right.obj.map f.op).hom ?_ ha
  exact congrArg CommRingCat.Hom.hom
    ((InducedCategory.Hom.hom A.obj.hom).naturality f.op)

private theorem isLocallyIntegral_of_isIntegral {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (U : smallEtaleSite X) {a : sectionRing A U}
    (ha : _root_.IsIntegral Γ(U.left.left, ⊤) a) : IsLocallyIntegral A U a := by
  refine ⟨Presieve.singleton (𝟙 U), ?_, ?_⟩
  · change (Presieve.singleton (𝟙 U)).map (smallEtaleToOver X) ∈
      (Scheme.overPretopology (@AlgebraicGeometry.Etale) S).toPrecoverage _
    rw [Presieve.map_singleton]
    exact (Scheme.overPretopology (@AlgebraicGeometry.Etale) S).has_isos _
  · intro V f hf
    cases hf
    simpa using ha

private theorem isLocallyIntegral_map {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (f : V ⟶ U)
    {a : sectionRing A U} (ha : IsLocallyIntegral A U a) :
    IsLocallyIntegral A V ((A.obj.right.obj.map f.op).hom a) := by
  obtain ⟨R, hR, ha⟩ := ha
  letI := smallEtalePrecoverage.hasPullbacks_of_mem f hR
  refine ⟨R.pullbackArrows f, smallEtalePrecoverage.pullbackArrows_mem f hR, ?_⟩
  intro W g hg
  cases hg with
  | mk W h hh =>
    letI := R.hasPullback f hh
    have he := congrArg (fun k ↦ (A.obj.right.obj.map k.op).hom a)
      (Limits.pullback.condition (f := h) (g := f)).symm
    simp only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply] at he
    rw [he]
    exact isIntegral_map A (Limits.pullback.fst h f) (ha h hh)

private theorem exists_cover_integral_pair {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (U : smallEtaleSite X) {a b : sectionRing A U}
    (ha : IsLocallyIntegral A U a) (hb : IsLocallyIntegral A U b) :
    ∃ R : Presieve U, R ∈ smallEtalePrecoverage X U ∧
      ∀ ⦃V : smallEtaleSite X⦄ (f : V ⟶ U), R f →
        _root_.IsIntegral Γ(V.left.left, ⊤) ((A.obj.right.obj.map f.op).hom a) ∧
        _root_.IsIntegral Γ(V.left.left, ⊤) ((A.obj.right.obj.map f.op).hom b) := by
  classical
  obtain ⟨R, hR, ha⟩ := ha
  have hb' (V : smallEtaleSite X) (f : V ⟶ U) (_ : R f) :=
    isLocallyIntegral_map A f hb
  choose T hT hb' using hb'
  refine ⟨R.bind (fun V f hf ↦ T V f hf),
    smallEtalePrecoverage.bind_mem hR (fun V f hf ↦ T V f hf) hT, ?_⟩
  rintro W g ⟨V, k, f, hf, hk, rfl⟩
  simpa only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply] using
    And.intro (isIntegral_map A k (ha f hf)) (hb' V f hf k hk)

private theorem isLocallyIntegral_of_cover {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) {U : smallEtaleSite X} (R : Presieve U)
    (hR : R ∈ smallEtalePrecoverage X U) {a : sectionRing A U}
    (ha : ∀ ⦃V : smallEtaleSite X⦄ (f : V ⟶ U), R f →
      IsLocallyIntegral A V ((A.obj.right.obj.map f.op).hom a)) :
    IsLocallyIntegral A U a := by
  classical
  choose T hT ha using fun V f hf ↦ @ha V f hf
  refine ⟨R.bind (fun V f hf ↦ T V f hf),
    smallEtalePrecoverage.bind_mem hR (fun V f hf ↦ T V f hf) hT, ?_⟩
  rintro W g ⟨V, k, f, hf, hk, rfl⟩
  simpa only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply] using
    ha V f hf k hk

/-- The sum of two locally integral sections is locally integral. -/
theorem isLocallyIntegral_add {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (U : smallEtaleSite X) {a b : sectionRing A U}
    (ha : IsLocallyIntegral A U a) (hb : IsLocallyIntegral A U b) :
    IsLocallyIntegral A U (a + b) := by
  obtain ⟨R, hR, hab⟩ := exists_cover_integral_pair A U ha hb
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  simpa only [map_add] using (hab f hf).1.add (hab f hf).2

/-- The product of two locally integral sections is locally integral. -/
theorem isLocallyIntegral_mul {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (U : smallEtaleSite X) {a b : sectionRing A U}
    (ha : IsLocallyIntegral A U a) (hb : IsLocallyIntegral A U b) :
    IsLocallyIntegral A U (a * b) := by
  obtain ⟨R, hR, hab⟩ := exists_cover_integral_pair A U ha hb
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  simpa only [map_mul] using (hab f hf).1.mul (hab f hf).2

/-- Every scalar section maps to a locally integral section. -/
theorem isLocallyIntegral_algebraMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (U : smallEtaleSite X) (r : Γ(U.left.left, ⊤)) :
    IsLocallyIntegral A U (algebraMap Γ(U.left.left, ⊤) (sectionRing A U) r) := by
  exact isLocallyIntegral_of_isIntegral A U isIntegral_algebraMap

/-- The subalgebra of locally integral sections of `A` over an étale object `U`. -/
def locallyIntegral {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) : Subalgebra Γ(U.left.left, ⊤) (sectionRing A U) where
  carrier := { a | IsLocallyIntegral A U a }
  add_mem' := isLocallyIntegral_add A U
  mul_mem' := isLocallyIntegral_mul A U
  algebraMap_mem' := isLocallyIntegral_algebraMap A U

/-- Membership in `locallyIntegral A U` is local integrality of the section. -/
theorem locallyIntegral_mem_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) {a : sectionRing A U} :
    a ∈ locallyIntegral A U ↔ IsLocallyIntegral A U a :=
  Iff.rfl

/-- Restriction along a morphism of étale objects preserves locally integral sections. -/
theorem locallyIntegral_map_mem {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    ∀ ⦃a : sectionRing A U⦄, a ∈ locallyIntegral A U →
      (A.obj.right.obj.map f.op).hom a ∈ locallyIntegral A V :=
  fun _ ha ↦ isLocallyIntegral_map A f ha

/-- The presheaf of locally integral sections of a quasi-coherent `𝒪_X`-algebra. -/
def integralClosureFunctor {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (locallyIntegral A U.unop)
  map {U V} f :=
    CommRingCat.ofHom
      (RingHom.restrict (A.obj.right.obj.map f).hom (locallyIntegral A U.unop)
        (locallyIntegral A V.unop) (locallyIntegral_map_mem A f.unop))
  map_id U := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply Subtype.ext
    change (A.obj.right.obj.map (𝟙 U)).hom a.val = a.val
    exact congrArg (fun h ↦ h.hom a.val) (A.obj.right.obj.map_id U)
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply Subtype.ext
    change (A.obj.right.obj.map (f ≫ g)).hom a.val =
      (A.obj.right.obj.map g).hom ((A.obj.right.obj.map f).hom a.val)
    exact congrArg (fun h ↦ h.hom a.val) (A.obj.right.obj.map_comp f g)

/-- The presheaf of locally integral sections is a sheaf on the small étale site. -/
theorem integralClosureFunctor_isSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    Presheaf.IsSheaf (smallEtaleTopology X) (integralClosureFunctor A) := by
  let i : integralClosureFunctor A ⟶ A.obj.right.obj :=
    { app := fun U ↦ CommRingCat.ofHom (locallyIntegral A U.unop).val.toRingHom
      naturality := by
        intro U V f
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        rfl }
  intro E
  let j := Functor.whiskerRight i (coyoneda.obj (op E))
  have hj (U) : Function.Injective (j.app U) := by
    intro g h he
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro e
    apply Subtype.ext
    exact congrArg (fun k ↦ k.hom e) he
  change Presieve.IsSheaf (smallEtalePrecoverage X).toGrothendieck _
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro U V f R hR
  letI := smallEtalePrecoverage.hasPullbacks_of_mem f hR
  rw [← Sieve.pullbackArrows_comm, ← Presieve.isSheafFor_iff_generate]
  have hR' := smallEtalePrecoverage.pullbackArrows_mem f hR
  have hA := (A.obj.right.property E).isSheafFor_of_mem_precoverage hR'
  intro x hx
  obtain ⟨t, ht, ht_unique⟩ := hA (x.map j) (hx.map j)
  have ht' (e : E) : IsLocallyIntegral A V (t.hom e) := by
    apply isLocallyIntegral_of_cover A _ hR'
    intro W k hk
    have he := congrArg (fun l ↦ l.hom e) (ht k hk)
    change (A.obj.right.obj.map k.op).hom (t.hom e) = ((x k hk).hom e).val at he
    rw [he]
    exact ((x k hk).hom e).property
  let s : E ⟶ (integralClosureFunctor A).obj (op V) :=
    CommRingCat.ofHom (RingHom.codRestrict t.hom (locallyIntegral A V) ht')
  have hs : j.app (op V) s = t := rfl
  refine ⟨s, ?_, ?_⟩
  · intro W k hk
    apply hj (op W)
    have he := congrArg (fun l ↦ l s) (j.naturality k.op)
    change j.app (op W) (((integralClosureFunctor A ⋙ coyoneda.obj (op E)).map k.op) s) =
      ((A.obj.right.obj ⋙ coyoneda.obj (op E)).map k.op) (j.app (op V) s) at he
    rw [hs] at he
    exact he.trans (ht k hk)
  · intro y hy
    apply hj (op V)
    rw [hs]
    exact ht_unique _ (hy.map j)

/-- The sheaf of locally integral sections of a quasi-coherent `𝒪_X`-algebra. -/
def integralClosureSheaf {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} where
  obj := integralClosureFunctor A
  property := integralClosureFunctor_isSheaf A

/-- The structure morphism from `𝒪_X` to the sheaf of locally integral sections of `A`. -/
def integralClosureStructure {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    commStructureSheaf X ⟶ integralClosureSheaf A :=
  InducedCategory.homMk
    { app := fun U ↦
        CommRingCat.ofHom (algebraMap Γ(U.unop.left.left, ⊤) (locallyIntegral A U.unop))
      naturality := by
        intro U V f
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro r
        apply Subtype.ext
        exact congrArg (fun h ↦ h.hom r)
          ((InducedCategory.Hom.hom A.obj.hom).naturality f) }

/-- On an affine étale chart, the locally integral subalgebra is the integral closure
of the structure ring inside the given section algebra. -/
theorem locallyIntegral_eq_integralClosure {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (U : affineEtaleSite X) :
    locallyIntegral A U.obj =
      _root_.integralClosure Γ(U.obj.left.left, ⊤) (sectionRing A U.obj) := by
  sorry

/-- The module underlying the algebra of locally integral sections is quasi-coherent. -/
theorem integralClosure_isQuasicoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    ((SheafOfModules.RingedSite.restrictionAlong (integralClosureStructure A)).obj
      (SheafOfModules.RingedSite.unitModule (smallEtaleTopology X)
        (integralClosureSheaf A))).IsQuasicoherent := by
  sorry

/-- The quasi-coherent `𝒪_X`-subalgebra of `A` obtained by taking locally integral sections. -/
def integralClosure {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    X.QcAlgebraUnder where
  obj := Under.mk (integralClosureStructure A)
  property := integralClosure_isQuasicoherent A

/-- The inclusion of locally integral sections, as a morphism of sheaves of algebras. -/
def inclusionRight {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    (integralClosure A).obj.right ⟶ A.obj.right :=
  InducedCategory.homMk
    { app := fun U ↦ CommRingCat.ofHom (locallyIntegral A U.unop).val.toRingHom
      naturality := by
        intro U V f
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        rfl }

/-- The structure morphism of `integralClosure A` factors as the inclusion into `A`. -/
theorem inclusionRight_w {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    (integralClosure A).obj.hom ≫ inclusionRight A = A.obj.hom := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  rfl

/-- The inclusion `integralClosure A ⟶ A` of quasi-coherent `𝒪_X`-algebras. -/
def inclusion {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    integralClosure A ⟶ A :=
  InducedCategory.homMk (Under.homMk (inclusionRight A) (inclusionRight_w A))

/-- On sections, the inclusion `integralClosure A ⟶ A` is the subtype inclusion of locally
integral sections. -/
theorem inclusion_app {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) :
    (InducedCategory.Hom.hom ((forget X).map (inclusion A)).right).app (op U) =
      CommRingCat.ofHom (locallyIntegral A U).val.toRingHom :=
  rfl

/-- On an affine étale chart, the section ring of the locally integral algebra is
its ring-theoretic integral closure. -/
theorem affine_sectionRing_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (U : affineEtaleSite X) :
    sectionRing (integralClosure A) U.obj =
      CommRingCat.of (_root_.integralClosure Γ(U.obj.left.left, ⊤) (sectionRing A U.obj)) := by
  change CommRingCat.of (locallyIntegral A U.obj) = _
  rw [locallyIntegral_eq_integralClosure A U]

/-- The inclusion of the locally integral algebra is a monomorphism on underlying sheaves. -/
@[instance]
theorem inclusion_mono {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    Mono ((forget X).map (inclusion A)).right := by
  constructor
  intro B g h w
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  apply Subtype.ext
  exact congrArg (fun k ↦ ((InducedCategory.Hom.hom k).app U).hom b) w

/-- Every quasi-coherent algebra contains a quasi-coherent subalgebra whose image on each
affine étale chart consists exactly of the sections integral over the structure ring. -/
theorem exists_integralClosure {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    ∃ (B : X.QcAlgebraUnder) (i : B ⟶ A),
      Mono ((forget X).map i).right ∧
      ∀ (U : affineEtaleSite X) (a : sectionRing A U.obj),
        (∃ b : sectionRing B U.obj,
          ((InducedCategory.Hom.hom (((forget X).map i).right)).app (op U.obj)).hom b = a) ↔
        _root_.IsIntegral Γ(U.obj.left.left, ⊤) a := by
  refine ⟨integralClosure A, inclusion A, inclusion_mono A, ?_⟩
  intro U a
  change (∃ b : locallyIntegral A U.obj, b.val = a) ↔ _
  rw [← _root_.mem_integralClosure_iff, ← locallyIntegral_eq_integralClosure A U]
  constructor
  · rintro ⟨b, rfl⟩
    exact b.property
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
