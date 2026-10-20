module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Logic.Small.Basic
public import Mathlib.Data.Quot
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Atlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Structure morphism of the finite-part functor

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` determines the
Type `u` functor `(X/Y)_fin` and the structure morphism `(X/Y)_fin ⟶ Y`,
together with its relative and absolute diagonals.

An open of `|T ×_Y X|` is an open subspace modulo isomorphism over the fibre
product, so sections of `(X/Y)_fin` compare as subspaces rather than as chosen
representatives.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A pair `(a, Z)` over a scheme `T` for a morphism `f : X ⟶ Y`: a morphism
`a : ofOver T ⟶ Y` and an open subspace `Z` of `T ×_Y X` whose restricted
projection to `T` is finite. -/
structure SubspacePoint (f : X ⟶ Y) (T : Over S) : Type (u + 1) where
  /-- The morphism `a : T ⟶ Y` over `S`. -/
  a : ofOver T ⟶ Y
  /-- The open subspace `Z ⊂ T ×_Y X`. -/
  Z : OpenSubspace (pullback a f)
  /-- The restricted projection `pr₀|_Z : Z ⟶ T` is finite. -/
  isFinite : IsFinite (Z.ι ≫ pullback.fst a f)

/-- Build a finite-part pair from a morphism `a : T ⟶ Y`, an open subspace of
`T ×_Y X`, and finiteness of the restricted first projection. -/
def SubspacePoint.of {f : X ⟶ Y} {T : Over S} (a : ofOver T ⟶ Y)
    (Z : OpenSubspace (pullback a f))
    (h : IsFinite (Z.ι ≫ pullback.fst a f)) : SubspacePoint f T where
  a := a
  Z := Z
  isFinite := h

/-- A finite-part pair is an open immersion into `T ×_Y X` whose restricted
first projection is finite. -/
theorem SubspacePoint.spec {f : X ⟶ Y} {T : Over S} (p : SubspacePoint f T) :
    IsOpenImmersion p.Z.ι ∧ IsFinite (p.Z.ι ≫ pullback.fst p.a f) :=
  ⟨p.Z.isOpenImmersion, p.isFinite⟩

/-- The functor-of-points element of `Y` determined by the morphism `a`. -/
def SubspacePoint.a_elem {f : X ⟶ Y} {T : Over S} (p : SubspacePoint f T) :
    Y.functorOfPoints.obj (op T) :=
  yonedaEquiv (p.a : yoneda.obj T ⟶ Y.functorOfPoints)

/-- Two finite-part pairs determine the same open of `|T ×_Y X|` when they share
the morphism `a` and their open subspaces are isomorphic over the fibre product. -/
def SubspacePoint.Rel (f : X ⟶ Y) (T : Over S) (p q : SubspacePoint f T) : Prop :=
  ∃ (ha : p.a = q.a) (e : p.Z.X ≅ q.Z.X), e.hom ≫ q.Z.ι = ha ▸ p.Z.ι

/-- Finite-part pairs modulo subspace equivalence. -/
def PointQuot (f : X ⟶ Y) (T : Over S) : Type (u + 1) :=
  Quot (SubspacePoint.Rel f T)

/-- The subspace class of a finite-part pair. -/
def PointQuot.mk {f : X ⟶ Y} {T : Over S} (p : SubspacePoint f T) : PointQuot f T :=
  Quot.mk (SubspacePoint.Rel f T) p

/-- Section equality of finite-part pairs is subspace equivalence. -/
theorem PointQuot.sound {f : X ⟶ Y} {T : Over S} {p q : SubspacePoint f T}
    (h : SubspacePoint.Rel f T p q) : PointQuot.mk p = PointQuot.mk q :=
  Quot.sound h

private theorem pointRel_equivalence (f : X ⟶ Y) (T : Over S) :
    Equivalence (SubspacePoint.Rel f T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨rfl, Iso.refl _, Category.id_comp _⟩
  · rintro ⟨a, Z, hZ⟩ ⟨b, W, hW⟩ ⟨h, e, he⟩
    cases h
    refine ⟨rfl, e.symm, ?_⟩
    change e.inv ≫ Z.ι = W.ι
    calc
      _ = e.inv ≫ (e.hom ≫ W.ι) := congrArg (fun k ↦ e.inv ≫ k) he.symm
      _ = W.ι := e.inv_hom_id_assoc _
  · rintro ⟨a, Z, hZ⟩ ⟨b, W, hW⟩ ⟨c, V, hV⟩ ⟨h, e, he⟩ ⟨h', e', he'⟩
    cases h
    cases h'
    refine ⟨rfl, e ≪≫ e', ?_⟩
    change (e.hom ≫ e'.hom) ≫ V.ι = Z.ι
    exact (Category.assoc _ _ _).trans ((congrArg (fun k ↦ e.hom ≫ k) he').trans he)

/-- Subspace classes of pairs agree if and only if the pairs are subspace
equivalent. -/
theorem PointQuot.mk_eq_iff {f : X ⟶ Y} {T : Over S} {p q : SubspacePoint f T} :
    PointQuot.mk p = PointQuot.mk q ↔ SubspacePoint.Rel f T p q :=
  Quot.eq.trans (pointRel_equivalence f T).eqvGen_iff

/-- Subspace-equivalent pairs determine the same `Y`-section. -/
theorem SubspacePoint.a_elem_rel {f : X ⟶ Y} {T : Over S} {p q : SubspacePoint f T}
    (h : SubspacePoint.Rel f T p q) : p.a_elem = q.a_elem := by
  exact congrArg (fun a : ofOver T ⟶ Y ↦ yonedaEquiv a) h.choose

/-- The `Y`-section of a subspace class of finite-part pairs. -/
def PointQuot.a_elem {f : X ⟶ Y} {T : Over S} (p : PointQuot f T) :
    Y.functorOfPoints.obj (op T) :=
  Quot.lift SubspacePoint.a_elem (fun _ _ h ↦ SubspacePoint.a_elem_rel h) p

/-- The `Y`-section of a subspace class recovers `SubspacePoint.a_elem`. -/
theorem PointQuot.a_elem_mk {f : X ⟶ Y} {T : Over S} (p : SubspacePoint f T) :
    (PointQuot.mk p).a_elem = p.a_elem := rfl

/-- The maps `pr₀ ≫ ofOverMap h` and `pr₁` out of `T' ×_Y X` agree over `Y`. -/
theorem baseChange_condition {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y)
    (a : ofOver T ⟶ Y) :
    (pullback.fst (ofOverMap h ≫ a) f ≫ ofOverMap h) ≫ a =
      pullback.snd (ofOverMap h ≫ a) f ≫ f :=
  (Category.assoc _ _ _).trans (pullback.condition)

/-- The comparison `h × id_X : T' ×_Y X ⟶ T ×_Y X` induced by `h : T' ⟶ T`. -/
def baseChange {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y) (a : ofOver T ⟶ Y) :
    pullback (ofOverMap h ≫ a) f ⟶ pullback a f :=
  pullback.lift (pullback.fst (ofOverMap h ≫ a) f ≫ ofOverMap h)
    (pullback.snd (ofOverMap h ≫ a) f) (baseChange_condition h f a)

/-- The base-change comparison commutes with the first projections. -/
theorem baseChange_fst {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y)
    (a : ofOver T ⟶ Y) :
    baseChange h f a ≫ pullback.fst a f =
      pullback.fst (ofOverMap h ≫ a) f ≫ ofOverMap h := by
  exact pullback.lift_fst _ _ _

/-- The base-change comparison commutes with the second projections. -/
theorem baseChange_snd {T T' : Over S} (h : T' ⟶ T) (f : X ⟶ Y)
    (a : ofOver T ⟶ Y) :
    baseChange h f a ≫ pullback.snd a f = pullback.snd (ofOverMap h ≫ a) f := by
  exact pullback.lift_snd _ _ _

/-- The inverse-image inclusion of an open subspace along `h × id_X` is an
open immersion. -/
theorem isOpenImmersion_restrictι {f : X ⟶ Y} {T T' : Over S}
    (p : SubspacePoint f T) (h : T' ⟶ T) :
    AlgebraicSpace.IsOpenImmersion (pullback.fst (baseChange h f p.a) p.Z.ι) :=
  sorry

/-- Base change along `h : T' ⟶ T` preserves finiteness of `pr₀|_Z`. -/
theorem restrict_isFinite {f : X ⟶ Y} {T T' : Over S} (p : SubspacePoint f T)
    (h : T' ⟶ T) :
    IsFinite
      (pullback.fst (baseChange h f p.a) p.Z.ι ≫
        pullback.fst (ofOverMap h ≫ p.a) f) :=
  sorry

/-- Base change of a pair `(a, Z)` along `h : T' ⟶ T`, sending `a` to `a ∘ h`
and `Z` to the inverse image `(h × id_X)⁻¹(Z) = T' ×_T Z`. -/
def SubspacePoint.restrict {f : X ⟶ Y} {T T' : Over S} (p : SubspacePoint f T) (h : T' ⟶ T) :
    SubspacePoint f T' :=
  SubspacePoint.of (ofOverMap h ≫ p.a)
    { X := pullback (baseChange h f p.a) p.Z.ι
      ι := pullback.fst (baseChange h f p.a) p.Z.ι
      isOpenImmersion := isOpenImmersion_restrictι p h }
    (restrict_isFinite p h)

/-- Inverse image preserves subspace equivalence of finite-part pairs. -/
theorem SubspacePoint.Rel.restrict {f : X ⟶ Y} {T T' : Over S} (h : T' ⟶ T)
    {p q : SubspacePoint f T} (hpq : SubspacePoint.Rel f T p q) :
    SubspacePoint.Rel f T' (p.restrict h) (q.restrict h) :=
  sorry

/-- Base change of a subspace class along `h : T' ⟶ T`. -/
def PointQuot.restrict {f : X ⟶ Y} {T T' : Over S} (p : PointQuot f T)
    (h : T' ⟶ T) : PointQuot f T' :=
  Quot.lift (fun p : SubspacePoint f T ↦ PointQuot.mk (p.restrict h))
    (fun _ _ hpq ↦ PointQuot.sound (SubspacePoint.Rel.restrict h hpq)) p

/-- Inverse image of a subspace class recovers the class of the inverse image. -/
theorem PointQuot.restrict_mk {f : X ⟶ Y} {T T' : Over S} (p : SubspacePoint f T)
    (h : T' ⟶ T) : (PointQuot.mk p).restrict h = PointQuot.mk (p.restrict h) := rfl

private theorem atlas_fppf_surjective (W : AlgebraicSpace S) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (AtlasInput.map W) := by
  apply Presheaf.isLocallySurjective_of_le (J := Scheme.etaleTopology.over S)
    (K := Scheme.fppfTopology.over S) ?_ (AtlasInput.map W) (AtlasInput.locallySurjective W)
  have h : Scheme.etaleTopology ≤ Scheme.fppfTopology :=
    Scheme.grothendieckTopology_monotone (fun A B i hi ↦
      ⟨inferInstanceAs (AlgebraicGeometry.Flat i),
        inferInstanceAs (AlgebraicGeometry.LocallyOfFinitePresentation i)⟩)
  intro A R hR
  exact h _ hR

private def rawCode {f : X ⟶ Y} {T : Over S} (p : SubspacePoint f T) :
    Σ a : ofOver T ⟶ Y, (AtlasInput.scheme (pullback a f)).left.Opens :=
  ⟨p.a, OpenSubspace.atlasOpens (AtlasInput.map (pullback p.a f)) p.Z⟩

private theorem rawCode_eq_iff {f : X ⟶ Y} {T : Over S} (p q : SubspacePoint f T) :
    rawCode p = rawCode q ↔ SubspacePoint.Rel f T p q := by
  rcases p with ⟨a, Z, hZ⟩
  rcases q with ⟨b, W, hW⟩
  constructor
  · intro h
    have hab : a = b := congrArg Sigma.fst h
    cases hab
    have ho : OpenSubspace.atlasOpens (AtlasInput.map (pullback a f)) Z =
        OpenSubspace.atlasOpens (AtlasInput.map (pullback a f)) W :=
      eq_of_heq (Sigma.mk.inj h).2
    obtain ⟨e, he⟩ := (OpenSubspace.atlasOpens_eq_iff _
      (atlas_fppf_surjective (pullback a f)) Z W).mp ho
    exact ⟨rfl, e, he⟩
  · rintro ⟨hab, e, he⟩
    cases hab
    change Sigma.mk a _ = Sigma.mk a _
    exact congrArg (Sigma.mk a) ((OpenSubspace.atlasOpens_eq_iff _
      (atlas_fppf_surjective (pullback a f)) Z W).mpr ⟨e, he⟩)

private def codeEquiv (f : X ⟶ Y) (T : Over S) :
    (Σ a : ofOver T ⟶ Y, (AtlasInput.scheme (pullback a f)).left.Opens) ≃
      (Σ a : Y.functorOfPoints.obj (op T),
        (AtlasInput.scheme (pullback (X := ofOver T) (yonedaEquiv.symm a) f)).left.Opens) :=
  Equiv.sigmaCongrLeft' yonedaEquiv

private def quotientCode (f : X ⟶ Y) (T : Over S) : PointQuot f T →
    (Σ a : Y.functorOfPoints.obj (op T),
      (AtlasInput.scheme (pullback (X := ofOver T) (yonedaEquiv.symm a) f)).left.Opens) :=
  Quot.lift (fun p ↦ codeEquiv f T (rawCode p))
    (fun p q h ↦ congrArg (codeEquiv f T) ((rawCode_eq_iff p q).mpr h))

private theorem quotientCode_injective (f : X ⟶ Y) (T : Over S) :
    Function.Injective (quotientCode f T) := by
  intro p q
  induction p using Quot.inductionOn with | h p =>
    induction q using Quot.inductionOn with | h q =>
      intro h
      exact PointQuot.sound ((rawCode_eq_iff p q).mp ((codeEquiv f T).injective h))

/-- The type of subspace classes of finite-part pairs over a scheme is small in the
universe of the scheme. -/
instance instSmall_pointQuot {f : X ⟶ Y} {T : Over S} :
    Small.{u} (PointQuot f T) :=
  small_of_injective (quotientCode_injective f T)

/-- Inverse image along the identity preserves a finite-part section. -/
theorem PointQuot.restrict_id {f : X ⟶ Y} {T : Over S} (p : PointQuot f T) :
    p.restrict (𝟙 T) = p := by
  sorry

/-- Inverse image of finite-part sections respects composition of scheme maps. -/
theorem PointQuot.restrict_comp {f : X ⟶ Y} {T T' T'' : Over S}
    (p : PointQuot f T) (h : T' ⟶ T) (k : T'' ⟶ T') :
    (p.restrict h).restrict k = p.restrict (k ≫ h) := by
  sorry

/-- The first component of a finite-part section restricts by the functor of points. -/
theorem PointQuot.a_elem_restrict {f : X ⟶ Y} {T T' : Over S}
    (p : PointQuot f T) (h : T' ⟶ T) :
    (p.restrict h).a_elem = Y.functorOfPoints.map h.op p.a_elem := by
  sorry

/-- The finite-part functor `(X/Y)_fin : (Over S)ᵒᵖ ⥤ Type u`. -/
def functor (f : X ⟶ Y) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (PointQuot f T.unop)
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      equivShrink (PointQuot f T'.unop)
        (((equivShrink (PointQuot f T.unop)).symm p).restrict h.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro p
    change equivShrink _ (((equivShrink _).symm p).restrict (𝟙 T.unop)) = p
    rw [PointQuot.restrict_id, Equiv.apply_symm_apply]
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro p
    change equivShrink _ (((equivShrink _).symm p).restrict (k.unop ≫ h.unop)) =
      equivShrink _ (((equivShrink _).symm
        (equivShrink _ (((equivShrink _).symm p).restrict h.unop))).restrict k.unop)
    rw [Equiv.symm_apply_apply, PointQuot.restrict_comp]

/-- Values of the finite-part functor are equivalent to subspace classes of
pairs `(a, Z)`. -/
def functor_obj_equiv (f : X ⟶ Y) (T : Over S) :
    (functor f).obj (op T) ≃ PointQuot f T :=
  (equivShrink (PointQuot f T)).symm

/-- Evaluating the finite-part functor at `T` recovers subspace classes of
pairs over `T`. -/
theorem functor_obj_equiv_apply (f : X ⟶ Y) {T : Over S}
    (p : (functor f).obj (op T)) :
    functor_obj_equiv f T p = (equivShrink (PointQuot f T)).symm p := rfl

/-- The structure morphism `(X/Y)_fin ⟶ Y`, sending a pair `(a, Z)` to the
`Y`-section `a`. -/
def hom (f : X ⟶ Y) : functor f ⟶ Y.functorOfPoints where
  app T := TypeCat.ofHom fun p ↦ (functor_obj_equiv f T.unop p).a_elem
  naturality T T' h := by
    ext p
    change ((equivShrink _).symm (equivShrink _
      (((equivShrink (PointQuot f T.unop)).symm p).restrict h.unop))).a_elem = _
    rw [Equiv.symm_apply_apply]
    exact PointQuot.a_elem_restrict _ _

/-- Components of `hom f` recover `PointQuot.a_elem`. -/
theorem hom_app (f : X ⟶ Y) (T : (Over S)ᵒᵖ) (p : (functor f).obj T) :
    (hom f).app T p = (functor_obj_equiv f T.unop p).a_elem := rfl

/-- On a pair `(a, Z)`, the structure morphism records `a` as `SubspacePoint.a_elem`. -/
theorem hom_spec (f : X ⟶ Y) {T : Over S} (p : SubspacePoint f T) :
    (hom f).app (op T) ((functor_obj_equiv f T).symm (PointQuot.mk p)) = p.a_elem := by
  change ((functor_obj_equiv f T) ((functor_obj_equiv f T).symm (PointQuot.mk p))).a_elem = _
  rw [Equiv.apply_symm_apply, PointQuot.a_elem_mk]

/-- The relative diagonal of `(X/Y)_fin ⟶ Y`. -/
abbrev diagonal (f : X ⟶ Y) : functor f ⟶ pullback (hom f) (hom f) :=
  pullback.diagonal (hom f)

/-- The relative diagonal of `(X/Y)_fin ⟶ Y` is the pullback diagonal of `hom f`. -/
theorem diagonal_eq (f : X ⟶ Y) : diagonal f = pullback.diagonal (hom f) := rfl

/-- The absolute diagonal of `(X/Y)_fin`. -/
abbrev diag (f : X ⟶ Y) : functor f ⟶ functor f ⨯ functor f :=
  Limits.diag (functor f)

/-- The absolute diagonal of `(X/Y)_fin` is the product diagonal of `(X/Y)_fin`. -/
theorem diag_eq (f : X ⟶ Y) : diag f = Limits.diag (functor f) := rfl


end AlgebraicGeometry.AlgebraicSpace.FinitePart
