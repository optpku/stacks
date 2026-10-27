/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.QuasiCompact.Sheaf

/-!
# Finite coproducts of quasi-compact sheaves

This file owns the coproduct-local-surjectivity and finite-coproduct closure
API for quasi-compact set-valued sheaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u v

namespace CategoryTheory.Sheaf.LocalSurjectivity

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A finite coproduct of componentwise locally surjective maps of sheaves is locally
surjective. -/
theorem sigmaDesc_of_componentwise
    {α : Type*} [Finite α]
    (Y F : α → Sheaf J (Type (max u v))) [HasCoproduct Y] [HasCoproduct F]
    (γ : ∀ a, Y a ⟶ F a)
    (hγ : ∀ a, IsLocallySurjective (γ a)) :
    IsLocallySurjective (Limits.Sigma.desc fun a ↦ γ a ≫ Limits.Sigma.ι F a) := by
  letI : ∀ a, Epi (γ a) := fun a ↦ (Sheaf.isLocallySurjective_iff_epi (γ a)).1 (hγ a)
  exact (Sheaf.isLocallySurjective_iff_epi (Limits.Sigma.map γ)).2 inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The coproduct local-surjectivity comparison for an index type small relative to the
ambient sheaf universe. -/
theorem sigmaDesc_iff_presheaf_of_small.{wι}
    {ι : Type wι} [Small.{max u v} ι] (X : ι → Sheaf J (Type (max u v)))
    {G : Sheaf J (Type (max u v))}
    (α : ∀ i, X i ⟶ G) [HasCoproduct X]
    [HasCoproduct fun i ↦ (X i).obj] :
    IsLocallySurjective (Limits.Sigma.desc α) ↔
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc fun i ↦ (α i).hom) := by
  let Q := ∐ fun i ↦ (X i).obj
  let a := Discrete.compNatIsoDiscrete X (sheafToPresheaf J (Type (max u v)))
  let c : Cocone (Discrete.functor X ⋙ sheafToPresheaf J (Type (max u v))) :=
    (Cocone.precompose a.hom).obj
      (Cofan.mk Q (fun i ↦ Sigma.ι (fun i ↦ (X i).obj) i))
  let hc : IsColimit c := (IsColimit.precomposeHomEquiv a _).symm
    (coproductIsCoproduct (fun i ↦ (X i).obj))
  let d := Sheaf.sheafifyCocone c
  let hd : IsColimit d := Sheaf.isColimitSheafifyCocone c hc
  let e := hd.coconePointUniqueUpToIso (coproductIsCoproduct X)
  let f : Q ⟶ G.obj := Sigma.desc fun i ↦ (α i).hom
  let g : (presheafToSheaf J (Type (max u v))).obj Q ⟶ G :=
    ((sheafificationAdjunction J (Type (max u v))).homEquiv Q G).symm f
  have fac : toSheafify J Q ≫ g.hom = f := by
    exact toSheafify_sheafifyLift J f G.property
  have he : e.hom ≫ Sigma.desc α = g := by
    apply hd.hom_ext
    rintro ⟨i⟩
    have hi : d.ι.app ⟨i⟩ ≫ g = α i := by
      apply Sheaf.hom_ext
      change (d.ι.app ⟨i⟩).hom ≫ g.hom = (α i).hom
      rw [Sheaf.sheafifyCocone_ι_app_val]
      change (Sigma.ι (fun i ↦ (X i).obj) i ≫ toSheafify J Q) ≫ g.hom = _
      rw [Category.assoc, fac]
      exact Sigma.ι_desc (fun i ↦ (α i).hom) i
    rw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact (Sigma.ι_desc α i).trans hi.symm
  change Presheaf.IsLocallySurjective J (Sigma.desc α).hom ↔ _
  calc
    Presheaf.IsLocallySurjective J (Sigma.desc α).hom ↔
        Presheaf.IsLocallySurjective J g.hom := by
      rw [← he]
      exact (Presheaf.comp_isLocallySurjective_iff J e.hom.hom (Sigma.desc α).hom).symm
    _ ↔ Presheaf.IsLocallySurjective J (toSheafify J Q ≫ g.hom) :=
      (Presheaf.comp_isLocallySurjective_iff J (toSheafify J Q) g.hom).symm
    _ ↔ Presheaf.IsLocallySurjective J f := by rw [fac]

/-- Local surjectivity of a coproduct map of sheaves is equivalent to local surjectivity
of its underlying presheaf coproduct map. -/
theorem sigmaDesc_iff_presheaf
    {ι : Type (max u v)} (X : ι → Sheaf J (Type (max u v)))
    {G : Sheaf J (Type (max u v))}
    (α : ∀ i, X i ⟶ G) [HasCoproduct X] :
    IsLocallySurjective (Limits.Sigma.desc α) ↔
      Presheaf.IsLocallySurjective J (Limits.Sigma.desc fun i ↦ (α i).hom) :=
  sigmaDesc_iff_presheaf_of_small X α

/-- Pulling back every summand of a locally surjective coproduct map preserves local
surjectivity of the resulting coproduct map. -/
theorem sigmaDesc_pullbackSnd
    {F G : Sheaf J (Type (max u v))} (q : F ⟶ G)
    {ι : Type (max u v)} (X : ι → Sheaf J (Type (max u v)))
    (α : ∀ i, X i ⟶ G)
    [HasCoproduct X] [HasCoproduct fun i ↦ pullback (α i) q]
    (hα : IsLocallySurjective (Limits.Sigma.desc α)) :
    IsLocallySurjective (Limits.Sigma.desc fun i ↦ pullback.snd (α i) q) := by
  let p := Sigma.desc fun i ↦ (α i).hom
  letI : Presheaf.IsLocallySurjective J p :=
    (Sheaf.LocalSurjectivity.sigmaDesc_iff_presheaf X α).1 hα
  rw [Sheaf.LocalSurjectivity.sigmaDesc_iff_presheaf]
  refine ⟨fun {U} s ↦ J.superset_covering ?_ (Presheaf.imageSieve_mem J p (q.hom.app (op U) s))⟩
  intro V f hf
  obtain ⟨t, ht⟩ := hf
  let E := (evaluation Cᵒᵖ (Type (max u v))).obj (op V)
  have hc := isColimitOfHasCoproductOfPreservesColimit E (fun i ↦ (X i).obj)
  obtain ⟨i, x, hx⟩ := Cofan.inj_jointly_surjective_of_isColimit hc t
  change (Sigma.ι (fun i ↦ (X i).obj) i).app (op V) x = t at hx
  have hxx : (α i).hom.app (op V) x =
      q.hom.app (op V) (F.obj.map f.op s) := by
    have hfac := ConcreteCategory.congr_hom
      (NatTrans.congr_app (Sigma.ι_desc (fun i ↦ (α i).hom) i) (op V)) x
    change _ = q.hom.app (op V) (F.obj.map f.op s)
    change ((Sigma.ι (fun i ↦ (X i).obj) i ≫ p).app (op V)) x = _ at hfac
    rw [NatTrans.comp_app, types_comp_apply] at hfac
    rw [← hfac, hx, ht]
    exact (q.hom.naturality_apply f.op s).symm
  have hp := (IsPullback.of_hasPullback (α i) q).map
    (sheafToPresheaf J (Type (max u v)) ⋙ E)
  obtain ⟨z, hz₁, hz₂⟩ := Types.exists_of_isPullback hp x (F.obj.map f.op s) hxx
  refine ⟨(Sigma.ι (fun i ↦ (pullback (α i) q).obj) i).app (op V) z, ?_⟩
  have hfac := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Sigma.ι_desc
      (fun i ↦ (pullback.snd (α i) q).hom) i) (op V)) z
  rw [NatTrans.comp_app, types_comp_apply] at hfac
  exact hfac.trans hz₂


end CategoryTheory.Sheaf.LocalSurjectivity

namespace CategoryTheory.Sheaf.IsQuasiCompactObject

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} [HasWeakSheafify J (Type (max u v))]

/-- Quasi-compact sheaf objects are stable under isomorphism. -/
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := sorry

/-- A finite coproduct of quasi-compact sheaves is quasi-compact. -/
theorem finiteCoproduct
    {α : Type*} [Finite α] (F : α → Sheaf J (Type (max u v))) [HasCoproduct F]
    (hF : ∀ a, IsQuasiCompactObject (F a)) :
    IsQuasiCompactObject (∐ F) := sorry

/-- Lemma 7.17.6 (0GMQ): quasi-compact sheaf objects are closed under finite coproducts. -/
@[stacks 0GMQ]
instance isClosedUnderFiniteCoproducts :
    ObjectProperty.IsClosedUnderFiniteCoproducts
      (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := sorry

end CategoryTheory.Sheaf.IsQuasiCompactObject
