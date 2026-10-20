module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Subcanonical
public import ReasLib.CategoryTheory.Sites.Family.Covering

/-!
# Local surjectivity for quotient sheaves of scheme pre-relations

For the standard topologies on schemes, equality in a quotient sheaf is characterized by
relation witnesses on a covering family. Consequently, the represented relation maps locally
surjectively onto the kernel pair of the quotient map.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- Equality in the universe-raised quotient is exactly the original point relation when the
pre-relation is a pre-equivalence relation. -/
private lemma uliftQuot_eq_iff_pointRel {S : Scheme.{u}} {U T : Over S}
    (P : PreRelation U) (hP : P.IsPreEquivalence) (x y : T ⟶ U) :
    ULift.up (Quot.mk (P.pointRel T) x) = ULift.up (Quot.mk (P.pointRel T) y) ↔
      P.pointRel T x y := by
  constructor
  · intro hxy
    have hmk : P.quotientMk.app (op T) x = P.quotientMk.app (op T) y := by
      change Quot.mk (P.pointRel T) x = Quot.mk (P.pointRel T) y
      exact congrArg ULift.down hxy
    exact (P.quotientMk_eq_iff_of_isPreEquivalence hP T x y).1 hmk
  · intro hxy
    have hmk : P.quotientMk.app (op T) x = P.quotientMk.app (op T) y :=
      (P.quotientMk_eq_iff_of_isPreEquivalence hP T x y).2 hxy
    change Quot.mk (P.pointRel T) x = Quot.mk (P.pointRel T) y at hmk
    exact congrArg ULift.up hmk

/-- Equality of quotient classes is equivalent to local point-relation data on a covering
family. -/
lemma quotientClass_eq_iff_exists_cover_pointRel {S : Scheme.{u}} (τ : StandardTopology)
    {U : Over S} (P : PreRelation U) (hP : P.IsPreEquivalence)
    (T : Over S) (a b : T ⟶ U) :
    P.quotientClass (τ.overTopology S) a = P.quotientClass (τ.overTopology S) b ↔
      ∃ 𝒳 : SemiRepresentableFamily.Over.{u + 1} T,
        SemiRepresentableFamily.Over.IsCovering (τ.overTopology S).toPrecoverage 𝒳 ∧
          ∀ i : 𝒳.index,
            P.pointRel ((𝒳.obj i).left) ((𝒳.obj i).hom ≫ a) ((𝒳.obj i).hom ≫ b) := by
  constructor
  · intro h
    let F := P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u}
    let x : F.obj (op T) := ULift.up (Quot.mk (P.pointRel T) a)
    let y : F.obj (op T) := ULift.up (Quot.mk (P.pointRel T) b)
    have hxy :
        (CategoryTheory.toSheafify (τ.overTopology S) F).app (op T) x =
          (CategoryTheory.toSheafify (τ.overTopology S) F).app (op T) y := by
      change P.quotientClass (τ.overTopology S) a = P.quotientClass (τ.overTopology S) b
      simpa [F, x, y, quotientClass_def] using h
    let α : F ⟶ CategoryTheory.sheafify (τ.overTopology S) F :=
      CategoryTheory.toSheafify (τ.overTopology S) F
    let hloc : CategoryTheory.Presheaf.IsLocallyInjective (τ.overTopology S) α := inferInstance
    change α.app (op T) x = α.app (op T) y at hxy
    let R : CategoryTheory.Sieve T := CategoryTheory.Presheaf.equalizerSieve (F := F) x y
    have hR : R ∈ τ.overTopology S T := hloc.equalizerSieve_mem x y hxy
    let 𝒢 : CategoryTheory.Presieve.GeneratingFamily R.arrows :=
      CategoryTheory.Presieve.GeneratingFamily.ofUncurry R.arrows
    refine ⟨𝒢.family, ?_, ?_⟩
    · rw [CategoryTheory.SemiRepresentableFamily.Over.isCovering_toPrecoverage_iff]
      simpa [CategoryTheory.SemiRepresentableFamily.Over.toSieve, 𝒢.generates,
        CategoryTheory.Sieve.generate_sieve] using hR
    · intro i
      have hi :
          F.map (𝒢.family.obj i).hom.op x = F.map (𝒢.family.obj i).hom.op y := by
        change R ((𝒢.family.obj i).hom)
        exact i.2
      have hquot :
          Quot.mk (P.pointRel ((𝒢.family.obj i).left)) ((𝒢.family.obj i).hom ≫ a) =
            Quot.mk (P.pointRel ((𝒢.family.obj i).left)) ((𝒢.family.obj i).hom ≫ b) := by
        change P.quotientPresheaf.map (𝒢.family.obj i).hom.op (Quot.mk (P.pointRel T) a) =
          P.quotientPresheaf.map (𝒢.family.obj i).hom.op (Quot.mk (P.pointRel T) b)
        rw [P.quotientPresheaf_map_mk, P.quotientPresheaf_map_mk]
        exact congrArg ULift.down hi
      exact (uliftQuot_eq_iff_pointRel P hP _ _).1
        (congrArg (ULift.up.{u + 1, u}) hquot)
  · rintro ⟨𝒳, h𝒳, hpoint⟩
    let xa : PUnit.{u + 2} ⟶ (P.quotientSheaf (τ.overTopology S)).1.obj (op T) :=
      TypeCat.ofHom (fun _ ↦ P.quotientClass (τ.overTopology S) a)
    let xb : PUnit.{u + 2} ⟶ (P.quotientSheaf (τ.overTopology S)).1.obj (op T) :=
      TypeCat.ofHom (fun _ ↦ P.quotientClass (τ.overTopology S) b)
    have hcover :
        CategoryTheory.Sieve.ofArrows (fun i : 𝒳.index ↦ (𝒳.obj i).left)
          (fun i ↦ (𝒳.obj i).hom) ∈ τ.overTopology S T := by
      simpa [CategoryTheory.SemiRepresentableFamily.Over.toSieve] using
        (CategoryTheory.SemiRepresentableFamily.Over.isCovering_toPrecoverage_iff
          (τ.overTopology S) 𝒳).1 h𝒳
    have hEq : xa = xb := by
      apply CategoryTheory.Presheaf.IsSheaf.hom_ext_ofArrows
        (hP := (P.quotientSheaf (τ.overTopology S)).2)
        (f := fun i : 𝒳.index ↦ (𝒳.obj i).hom)
        (hf := hcover)
      intro i
      apply ConcreteCategory.hom_ext
      intro z
      cases z
      simp only [xa, xb, comp_apply]
      calc
        (P.quotientSheaf (τ.overTopology S)).1.map (𝒳.obj i).hom.op
            (P.quotientClass (τ.overTopology S) a) =
          P.quotientClass (τ.overTopology S) ((𝒳.obj i).hom ≫ a) :=
            quotientClass_map (τ.overTopology S) P (𝒳.obj i).hom a
        _ = P.quotientClass (τ.overTopology S) ((𝒳.obj i).hom ≫ b) := by
          rw [quotientClass_def, quotientClass_def]
          exact congrArg
            ((CategoryTheory.toSheafify (τ.overTopology S)
              (P.quotientPresheaf ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).app
                (op ((𝒳.obj i).left)))
            ((uliftQuot_eq_iff_pointRel P hP _ _).2 (hpoint i))
        _ = (P.quotientSheaf (τ.overTopology S)).1.map (𝒳.obj i).hom.op
              (P.quotientClass (τ.overTopology S) b) := by
          symm
          exact quotientClass_map (τ.overTopology S) P (𝒳.obj i).hom b
    exact ConcreteCategory.congr_hom hEq PUnit.unit

/-- Two points have the same class in the quotient sheaf exactly when a covering family makes
them the source and target of local arrows in the pre-equivalence relation. -/
theorem quotientClass_eq_iff_exists_cover {S : Scheme.{u}} (τ : StandardTopology)
    {U : Over S} (P : PreRelation U) (hP : P.IsPreEquivalence)
    (T : Over S) (a b : T ⟶ U) :
    P.quotientClass (τ.overTopology S) a = P.quotientClass (τ.overTopology S) b ↔
      ∃ 𝒳 : SemiRepresentableFamily.Over.{u + 1} T,
        SemiRepresentableFamily.Over.IsCovering (τ.overTopology S).toPrecoverage 𝒳 ∧
          ∀ i : 𝒳.index, ∃ r : (𝒳.obj i).left ⟶ P.left,
            (𝒳.obj i).hom ≫ a = r ≫ P.s ∧
              (𝒳.obj i).hom ≫ b = r ≫ P.t := by
  constructor
  · rintro h
    rcases (quotientClass_eq_iff_exists_cover_pointRel τ P hP T a b).1 h with
      ⟨𝒳, h𝒳, hpoint⟩
    refine ⟨𝒳, h𝒳, ?_⟩
    intro i
    have hsym :
        P.pointRel ((𝒳.obj i).left) ((𝒳.obj i).hom ≫ b) ((𝒳.obj i).hom ≫ a) :=
      (hP ((𝒳.obj i).left)).symm (hpoint i)
    rw [P.pointRel_iff] at hsym
    rcases hsym with ⟨r, hrb, hra⟩
    exact ⟨r, hra.symm, hrb.symm⟩
  · rintro ⟨𝒳, h𝒳, hwit⟩
    refine (quotientClass_eq_iff_exists_cover_pointRel τ P hP T a b).2 ⟨𝒳, h𝒳, ?_⟩
    intro i
    rcases hwit i with ⟨r, hra, hrb⟩
    have hswap :
        P.pointRel ((𝒳.obj i).left) ((𝒳.obj i).hom ≫ b) ((𝒳.obj i).hom ≫ a) := by
      rw [P.pointRel_iff]
      exact ⟨r, hrb.symm, hra.symm⟩
    exact (hP ((𝒳.obj i).left)).symm hswap

/-- A morphism into the kernel pair is determined by its two projections to the represented
source and target maps of the pre-relation. -/
private lemma relationToKernelPair_eq_of_proj_eq {S : Scheme.{u}} {U T : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U)
    (σ : J.uliftYoneda.obj T ⟶ pullback (P.quotientMap J) (P.quotientMap J)) (r : T ⟶ P.left)
    (hfst : σ ≫ pullback.fst (P.quotientMap J) (P.quotientMap J) = J.uliftYoneda.map (r ≫ P.s))
    (hsnd : σ ≫ pullback.snd (P.quotientMap J) (P.quotientMap J) = J.uliftYoneda.map (r ≫ P.t)) :
    σ = J.uliftYoneda.map r ≫ P.relationToKernelPair J := by
  apply pullback.hom_ext
  · calc
      σ ≫ pullback.fst (P.quotientMap J) (P.quotientMap J) = J.uliftYoneda.map (r ≫ P.s) := hfst
      _ = J.uliftYoneda.map r ≫ J.uliftYoneda.map P.s := by
          rw [← J.uliftYoneda.map_comp]
      _ = J.uliftYoneda.map r ≫ P.relationToKernelPair J ≫
            pullback.fst (P.quotientMap J) (P.quotientMap J) := by
          exact Eq.symm <| by
            simpa [Category.assoc] using
              congrArg (fun k => J.uliftYoneda.map r ≫ k)
                (P.relationToKernelPair_fst (J := J))
  · calc
      σ ≫ pullback.snd (P.quotientMap J) (P.quotientMap J) = J.uliftYoneda.map (r ≫ P.t) := hsnd
      _ = J.uliftYoneda.map r ≫ J.uliftYoneda.map P.t := by
          rw [← J.uliftYoneda.map_comp]
      _ = J.uliftYoneda.map r ≫ P.relationToKernelPair J ≫
            pullback.snd (P.quotientMap J) (P.quotientMap J) := by
          exact Eq.symm <| by
            simpa [Category.assoc] using
              congrArg (fun k => J.uliftYoneda.map r ≫ k)
                (P.relationToKernelPair_snd (J := J))

/-- A represented local witness whose two projections match a restricted pullback section
produces membership in the image sieve of `relationToKernelPair`. -/
private lemma imageSieve_mem_relationToKernelPair_of_proj_eq
    {S : Scheme.{u}} {U T V : Over S}
    (J : GrothendieckTopology (Over S)) [J.Subcanonical] (P : PreRelation U)
    (x : (pullback
      ((P.quotientMap J) : J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J)
      ((P.quotientMap J) : J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J)).obj.obj (op T))
    (g : V ⟶ T) (r : V ⟶ P.left)
    (hfst : J.uliftYoneda.{u + 1}.map g ≫ J.uliftYonedaEquiv.{u + 1}.symm x ≫
        pullback.fst
          ((P.quotientMap J) : J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J)
          ((P.quotientMap J) : J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J) =
      J.uliftYoneda.{u + 1}.map (r ≫ P.s))
    (hsnd : J.uliftYoneda.{u + 1}.map g ≫ J.uliftYonedaEquiv.{u + 1}.symm x ≫
        pullback.snd
          ((P.quotientMap J) : J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J)
          ((P.quotientMap J) : J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J) =
      J.uliftYoneda.{u + 1}.map (r ≫ P.t)) :
    Presheaf.imageSieve (P.relationToKernelPair J).hom x g := by
  let q : J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J := P.quotientMap J
  let σ : J.uliftYoneda.{u + 1}.obj T ⟶ pullback q q :=
    J.uliftYonedaEquiv.{u + 1}.symm x
  have hσ :
      J.uliftYoneda.{u + 1}.map g ≫ σ = J.uliftYoneda.{u + 1}.map r ≫
        P.relationToKernelPair J := by
    exact relationToKernelPair_eq_of_proj_eq J P (J.uliftYoneda.map g ≫ σ) r hfst hsnd
  refine ⟨ULift.up r, ?_⟩
  calc
    (P.relationToKernelPair J).hom.app (op V) (ULift.up r) =
        J.uliftYonedaEquiv.{u + 1} (J.uliftYoneda.{u + 1}.map r ≫
          P.relationToKernelPair J) := by
          symm
          exact J.uliftYonedaEquiv_comp _ _
    _ = J.uliftYonedaEquiv.{u + 1} (J.uliftYoneda.{u + 1}.map g ≫ σ) := by rw [hσ.symm]
    _ = (pullback q q).obj.map g.op x := by
          symm
          simpa [q, σ] using J.uliftYonedaEquiv_naturality (f := σ) g

/-- The represented relation maps locally surjectively onto the kernel pair of the quotient
map. -/
theorem relationToKernelPair_locallySurjective {S : Scheme.{u}} (τ : StandardTopology)
    {U : Over S} (P : PreRelation U) (hP : P.IsPreEquivalence) :
    Sheaf.IsLocallySurjective (P.relationToKernelPair (τ.overTopology S)) := by
  let J : GrothendieckTopology (Over S) := τ.overTopology S
  change Presheaf.IsLocallySurjective J (P.relationToKernelPair J).hom
  refine ⟨?_⟩
  intro T x
  let q : J.uliftYoneda.{u + 1}.obj U ⟶ P.quotientSheaf J := P.quotientMap J
  let σ : J.uliftYoneda.{u + 1}.obj T ⟶ pullback q q :=
    J.uliftYonedaEquiv.{u + 1}.symm x
  let a : T ⟶ U := (J.uliftYonedaEquiv.{u + 1} (σ ≫ pullback.fst q q)).down
  let b : T ⟶ U := (J.uliftYonedaEquiv.{u + 1} (σ ≫ pullback.snd q q)).down
  have hfst_repr :
      σ ≫ pullback.fst q q = J.uliftYoneda.{u + 1}.map a := by
    apply J.uliftYonedaEquiv.{u + 1}.injective
    rw [J.uliftYonedaEquiv_uliftYoneda_map]
    cases h : J.uliftYonedaEquiv.{u + 1} (σ ≫ pullback.fst q q) with
    | up v =>
        simp [a, h]
  have hsnd_repr :
      σ ≫ pullback.snd q q = J.uliftYoneda.{u + 1}.map b := by
    apply J.uliftYonedaEquiv.{u + 1}.injective
    rw [J.uliftYonedaEquiv_uliftYoneda_map]
    cases h : J.uliftYonedaEquiv.{u + 1} (σ ≫ pullback.snd q q) with
    | up v =>
        simp [b, h]
  have hpull :
      σ ≫ pullback.fst q q ≫ q =
        σ ≫ pullback.snd q q ≫ q := by
    have hcond : pullback.fst q q ≫ q = pullback.snd q q ≫ q := pullback.condition
    simpa [Category.assoc] using congrArg (fun k => σ ≫ k) hcond
  have hclass : P.quotientClass J a = P.quotientClass J b := by
    have hmap :
        J.uliftYoneda.{u + 1}.map a ≫ P.quotientMap J =
          J.uliftYoneda.{u + 1}.map b ≫ P.quotientMap J := by
      calc
        J.uliftYoneda.{u + 1}.map a ≫ P.quotientMap J = σ ≫ pullback.fst q q ≫ q := by
          simpa [q, Category.assoc] using congrArg (fun k => k ≫ q) hfst_repr.symm
        _ = σ ≫ pullback.snd q q ≫ q := hpull
        _ = J.uliftYoneda.{u + 1}.map b ≫ P.quotientMap J := by
          simpa [q, Category.assoc] using congrArg (fun k => k ≫ q) hsnd_repr
    have hmap' := congrArg (fun k => J.uliftYonedaEquiv.{u + 1} k) hmap
    rw [J.uliftYonedaEquiv_comp, J.uliftYonedaEquiv_comp,
      J.uliftYonedaEquiv_uliftYoneda_map, J.uliftYonedaEquiv_uliftYoneda_map] at hmap'
    change (P.quotientMap J).hom.app (op T) (ULift.up a) =
      (P.quotientMap J).hom.app (op T) (ULift.up b) at hmap'
    rw [quotientMap_app, quotientMap_app] at hmap'
    exact hmap'
  rcases (quotientClass_eq_iff_exists_cover τ P hP T a b).1 hclass with
    ⟨𝒳, h𝒳, hwit⟩
  have hcover : 𝒳.toSieve ∈ J T := by
    exact (CategoryTheory.SemiRepresentableFamily.Over.isCovering_toPrecoverage_iff J 𝒳).1 h𝒳
  have hle : 𝒳.toSieve ≤ Presheaf.imageSieve (P.relationToKernelPair J).hom x := by
    rw [CategoryTheory.SemiRepresentableFamily.Over.toSieve,
      CategoryTheory.Sieve.generate_le_iff]
    intro V g hg
    rcases (CategoryTheory.Presieve.ofArrows_surj
        (Y := fun i : 𝒳.index ↦ (𝒳.obj i).left)
        (f := fun i ↦ (𝒳.obj i).hom) (g := g) hg) with
      ⟨i, hiObj, hiArrow⟩
    subst hiObj
    simp only [eqToHom_refl, Category.id_comp] at hiArrow
    subst hiArrow
    rcases hwit i with ⟨r, hra, hrb⟩
    have hlocal_fst :
        J.uliftYoneda.{u + 1}.map (𝒳.obj i).hom ≫ σ ≫
            pullback.fst q q =
          J.uliftYoneda.{u + 1}.map (r ≫ P.s) := by
      calc
        J.uliftYoneda.{u + 1}.map (𝒳.obj i).hom ≫ σ ≫
            pullback.fst q q =
          J.uliftYoneda.{u + 1}.map (𝒳.obj i).hom ≫ J.uliftYoneda.{u + 1}.map a := by
            simpa [Category.assoc] using
              congrArg (fun k => J.uliftYoneda.{u + 1}.map (𝒳.obj i).hom ≫ k) hfst_repr
        _ = J.uliftYoneda.{u + 1}.map ((𝒳.obj i).hom ≫ a) := by
            rw [← J.uliftYoneda.map_comp]
        _ = J.uliftYoneda.{u + 1}.map (r ≫ P.s) := by rw [hra]
    have hlocal_snd :
        J.uliftYoneda.{u + 1}.map (𝒳.obj i).hom ≫ σ ≫
            pullback.snd q q =
          J.uliftYoneda.{u + 1}.map (r ≫ P.t) := by
      calc
        J.uliftYoneda.{u + 1}.map (𝒳.obj i).hom ≫ σ ≫
            pullback.snd q q =
          J.uliftYoneda.{u + 1}.map (𝒳.obj i).hom ≫ J.uliftYoneda.{u + 1}.map b := by
            simpa [Category.assoc] using
              congrArg (fun k => J.uliftYoneda.{u + 1}.map (𝒳.obj i).hom ≫ k) hsnd_repr
        _ = J.uliftYoneda.{u + 1}.map ((𝒳.obj i).hom ≫ b) := by
            rw [← J.uliftYoneda.map_comp]
        _ = J.uliftYoneda.{u + 1}.map (r ≫ P.t) := by rw [hrb]
    exact imageSieve_mem_relationToKernelPair_of_proj_eq J P x (𝒳.obj i).hom r
      hlocal_fst hlocal_snd
  exact J.superset_covering hle hcover

end AlgebraicGeometry.Scheme.PreRelation
