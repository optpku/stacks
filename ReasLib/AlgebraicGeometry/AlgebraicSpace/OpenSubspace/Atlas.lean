/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Open subspaces detected on a scheme atlas

The pullback of an open subspace to a scheme is an open subscheme. A locally
surjective scheme atlas detects isomorphism of open subspaces over their ambient space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {A : Over S}

/-- The open subset of a scheme obtained by pulling back an open subspace along a morphism
from that scheme. -/
def atlasOpens (p : ofOver A ⟶ X) (U : OpenSubspace X) : A.left.Opens :=
  ⟨Set.range (U.isOpenImmersion.presheaf.rep.snd p).left,
    (U.isOpenImmersion.presheaf.property_snd p).base_open.isOpen_range⟩

/-- The open subset obtained by scheme base change is the range of the represented
pullback projection. -/
theorem atlasOpens_spec (p : ofOver A ⟶ X) (U : OpenSubspace X) :
    (atlasOpens p U : Set A.left) =
      Set.range (U.isOpenImmersion.presheaf.rep.snd p).left := rfl

private theorem inclusion_mono (U : OpenSubspace X) :
    Mono (C := (Over S)ᵒᵖ ⥤ Type u) U.ι := by
  apply MorphismProperty.presheaf_monomorphisms_le_monomorphisms
  apply MorphismProperty.relative_monotone (P := MorphismProperty.over
    (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u}))
    (fun B C i hi ↦ ?_) _ U.isOpenImmersion.presheaf
  have h : AlgebraicGeometry.IsOpenImmersion i.left := hi
  exact (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono i.left))

private theorem range_isSheaf (U : OpenSubspace X) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) (Subfunctor.range U.ι).toFunctor := by
  have hm := inclusion_mono U
  apply Presieve.isSheaf_iso (Scheme.fppfTopology.over S) (asIso (Subfunctor.toRange U.ι))
  exact (isSheaf_iff_isSheaf_of_type _ _).mp U.X.isSheaf

private def atlasIso (p : ofOver A ⟶ X) (U V : OpenSubspace X)
    (h : atlasOpens p U = atlasOpens p V) :
    U.isOpenImmersion.presheaf.rep.pullback p ≅
      V.isOpenImmersion.presheaf.rep.pullback p := by
  let qU := U.isOpenImmersion.presheaf.rep.snd p
  let qV := V.isOpenImmersion.presheaf.rep.snd p
  have hU : AlgebraicGeometry.IsOpenImmersion qU.left :=
    U.isOpenImmersion.presheaf.property_snd p
  have hV : AlgebraicGeometry.IsOpenImmersion qV.left :=
    V.isOpenImmersion.presheaf.property_snd p
  let e := AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq qU.left qV.left
    (congrArg (fun O : A.left.Opens ↦ (O : Set A.left)) h)
  refine Over.isoMk e ?_
  rw [← qV.w, ← Category.assoc,
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac, qU.w]

private theorem atlasIso_snd (p : ofOver A ⟶ X) (U V : OpenSubspace X)
    (h : atlasOpens p U = atlasOpens p V) :
    (atlasIso p U V h).hom ≫ V.isOpenImmersion.presheaf.rep.snd p =
      U.isOpenImmersion.presheaf.rep.snd p := by
  have hU : AlgebraicGeometry.IsOpenImmersion
      (U.isOpenImmersion.presheaf.rep.snd p).left :=
    U.isOpenImmersion.presheaf.property_snd p
  have hV : AlgebraicGeometry.IsOpenImmersion
      (V.isOpenImmersion.presheaf.rep.snd p).left :=
    V.isOpenImmersion.presheaf.property_snd p
  apply Over.OverMorphism.ext
  exact AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _
    (congrArg (fun O : A.left.Opens ↦ (O : Set A.left)) h)

private theorem range_le_of_atlasOpens_eq (p : ofOver A ⟶ X)
    (hp : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) p)
    (U V : OpenSubspace X) (h : atlasOpens p U = atlasOpens p V) :
    Subfunctor.range U.ι ≤ Subfunctor.range V.ι := by
  intro B x hx
  have hV := (Subfunctor.isSheaf_iff (Subfunctor.range V.ι)
    ((isSheaf_iff_isSheaf_of_type _ _).mp X.isSheaf)).mp (range_isSheaf V)
  apply hV B x
  apply (Scheme.fppfTopology.over S).superset_covering ?_ (hp.imageSieve_mem x)
  intro C i hi
  obtain ⟨t, ht⟩ := hi
  obtain ⟨z, hz⟩ := (Subfunctor.range U.ι).map i.op hx
  let rU := U.isOpenImmersion.presheaf.rep
  let rV := V.isOpenImmersion.presheaf.rep
  obtain ⟨w, hw₁, hw₂⟩ := Types.exists_of_isPullback
    ((rU.isPullback p).map ((evaluation _ _).obj (op C))) z t (hz.trans ht.symm)
  refine ⟨rV.fst p |>.app (op C) ((yoneda.map (atlasIso p U V h).hom).app _ w), ?_⟩
  have hw := congrArg (fun k ↦ k.app (op C)
    ((yoneda.map (atlasIso p U V h).hom).app _ w)) (rV.w p)
  refine (show V.ι.app _ _ = _ from hw).trans ?_
  have he := congrArg (fun k ↦ (yoneda.map k).app (op C) w) (atlasIso_snd p U V h)
  change (yoneda.map (rU.snd p)).app (op C) w = t at hw₂
  exact (congrArg (fun t ↦ p.app (op C) t) he).trans
    ((congrArg (fun t ↦ p.app (op C) t) hw₂).trans ht)

private theorem iso_of_range_eq (U V : OpenSubspace X)
    (h : Subfunctor.range U.ι = Subfunctor.range V.ι) :
    ∃ e : U.X ≅ V.X, e.hom ≫ V.ι = U.ι := by
  have hmU := inclusion_mono U
  have hmV := inclusion_mono V
  have hi : ∀ {R R' : Subfunctor X.functorOfPoints} (h : R = R'),
      eqToHom (congrArg Subfunctor.toFunctor h) ≫ R'.ι = R.ι := by
    intro R R' h
    cases h
    simp
  have hv : inv (Subfunctor.toRange V.ι) ≫ V.ι = (Subfunctor.range V.ι).ι := by
    calc
      _ = inv (Subfunctor.toRange V.ι) ≫
          (Subfunctor.toRange V.ι ≫ (Subfunctor.range V.ι).ι) :=
        congrArg (fun k ↦ inv (Subfunctor.toRange V.ι) ≫ k)
          (Subfunctor.toRange_ι V.ι).symm
      _ = _ := IsIso.inv_hom_id_assoc _ _
  let e : U.X.functorOfPoints ≅ V.X.functorOfPoints :=
    asIso (Subfunctor.toRange U.ι) ≪≫
      eqToIso (congrArg Subfunctor.toFunctor h) ≪≫ (asIso (Subfunctor.toRange V.ι)).symm
  have he : e.hom ≫ V.ι = U.ι := by
    change (Subfunctor.toRange U.ι ≫ eqToHom (congrArg Subfunctor.toFunctor h) ≫
      inv (Subfunctor.toRange V.ι)) ≫ V.ι = U.ι
    calc
      _ = Subfunctor.toRange U.ι ≫ (eqToHom (congrArg Subfunctor.toFunctor h) ≫
          (inv (Subfunctor.toRange V.ι) ≫ V.ι)) := by simp only [Category.assoc]
      _ = Subfunctor.toRange U.ι ≫ (eqToHom (congrArg Subfunctor.toFunctor h) ≫
          (Subfunctor.range V.ι).ι) :=
        congrArg (fun k ↦ Subfunctor.toRange U.ι ≫
          (eqToHom (congrArg Subfunctor.toFunctor h) ≫ k)) hv
      _ = Subfunctor.toRange U.ι ≫ (Subfunctor.range U.ι).ι :=
        congrArg (fun k ↦ Subfunctor.toRange U.ι ≫ k) (hi h)
      _ = U.ι := Subfunctor.toRange_ι U.ι
  let e' : U.X ≅ V.X :=
    { hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id }
  exact ⟨e', he⟩

/-- A morphism from a scheme that is fppf-locally surjective detects when two open
subspaces are isomorphic over their ambient algebraic space. -/
theorem atlasOpens_eq_iff (p : ofOver A ⟶ X)
    (hp : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) p)
    (U V : OpenSubspace X) :
    atlasOpens p U = atlasOpens p V ↔
      ∃ e : U.X ≅ V.X, e.hom ≫ V.ι = U.ι := by
  constructor
  · intro h
    exact iso_of_range_eq U V (le_antisymm
      (range_le_of_atlasOpens_eq p hp U V h)
      (range_le_of_atlasOpens_eq p hp V U h.symm))
  · rintro ⟨e, he⟩
    let eh : U.X.functorOfPoints ⟶ V.X.functorOfPoints := e.hom
    let ei : V.X.functorOfPoints ⟶ U.X.functorOfPoints := e.inv
    have he' : eh ≫ V.ι = U.ι := he
    have hei : ei ≫ U.ι = V.ι := by
      calc
        _ = ei ≫ eh ≫ V.ι := congrArg (fun k ↦ ei ≫ k) he'.symm
        _ = V.ι := e.inv_hom_id_assoc _
    let rU := U.isOpenImmersion.presheaf.rep
    let rV := V.isOpenImmersion.presheaf.rep
    let l : rU.pullback p ⟶ rV.pullback p := rV.lift (rU.fst p ≫ eh) (rU.snd p)
      ((Category.assoc _ _ _).trans ((congrArg (fun k ↦ rU.fst p ≫ k) he').trans (rU.w p)))
    let k : rV.pullback p ⟶ rU.pullback p := rU.lift (rV.fst p ≫ ei) (rV.snd p)
      ((Category.assoc _ _ _).trans ((congrArg (fun k ↦ rV.fst p ≫ k) hei).trans (rV.w p)))
    apply TopologicalSpace.Opens.ext
    apply Set.Subset.antisymm
    · rintro _ ⟨w, rfl⟩
      exact ⟨l.left w, congrArg (fun t : rU.pullback p ⟶ A ↦ t.left w)
        (rV.lift_snd (rU.fst p ≫ eh) (rU.snd p) _ )⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨k.left w, congrArg (fun t : rV.pullback p ⟶ A ↦ t.left w)
        (rU.lift_snd (rV.fst p ≫ ei) (rV.snd p) _ )⟩

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
