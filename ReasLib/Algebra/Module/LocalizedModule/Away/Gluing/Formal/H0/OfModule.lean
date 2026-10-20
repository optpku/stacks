/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.H0
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.OfModule
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-Zero Recovery of Canonical Formal Gluing

A source module maps canonically to the degree-zero module of its formal
gluing datum.  For a finite principal-open family, a flat ring map inducing a
bijective quotient map makes this unit an isomorphism.

@stack 05EL
@stack 05EM
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type v}

/-- The ambient map underlying the unit from a module to `H⁰` of its
canonical formal gluing datum.  Its two components are scalar extension and
the compatible family of principal-open restrictions. -/
@[stacks 05EL "canonical formal gluing degree-zero ambient unit",
  stacks 05EM "canonical formal gluing degree-zero ambient unit"]
noncomputable def h0UnitAmbient (φ : R →+* S) (f : ι → R)
    (M : ModuleCat.{max u v} R) :
    M →ₗ[R] (ofModule φ f M).h0Source :=
  LinearMap.prod
    (ModuleCat.ExtendRestrictScalarsAdj.Unit.map φ).hom
    (Gluing.ofModuleSection f M)

/-- The ambient degree-zero unit evaluates to the scalar-extension unit and
the compatible principal-open section attached to the same element. -/
@[simp, stacks 05EL "canonical formal gluing degree-zero ambient unit application",
  stacks 05EM "canonical formal gluing degree-zero ambient unit application"]
theorem h0UnitAmbient_apply (φ : R →+* S) (f : ι → R)
    (M : ModuleCat.{max u v} R) (m : M) :
    h0UnitAmbient φ f M m =
      ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map φ).hom m,
        Gluing.ofModuleSection f M m) := sorry

/-- The ambient unit satisfies every global-versus-local compatibility
equation defining degree-zero formal-gluing sections. -/
@[stacks 05EL "canonical formal gluing degree-zero unit compatibility",
  stacks 05EM "canonical formal gluing degree-zero unit compatibility"]
theorem h0Unit_mem (φ : R →+* S) (f : ι → R)
    (M : ModuleCat.{max u v} R) (m : M) :
    h0UnitAmbient φ f M m ∈ (ofModule φ f M).h0Module := sorry

/-- The canonical unit from a module to the degree-zero module of its formal
gluing datum. -/
@[stacks 05EL "canonical formal gluing degree-zero unit",
  stacks 05EM "canonical formal gluing degree-zero unit"]
noncomputable def h0Unit (φ : R →+* S) (f : ι → R)
    (M : ModuleCat.{max u v} R) :
    M →ₗ[R] (ofModule φ f M).h0Module :=
  LinearMap.codRestrict (ofModule φ f M).h0Module
    (h0UnitAmbient φ f M) (h0Unit_mem φ f M)

/-- Forgetting the kernel membership certificate from the degree-zero unit
recovers its ambient two-component map. -/
@[simp, stacks 05EL "canonical formal gluing degree-zero unit application",
  stacks 05EM "canonical formal gluing degree-zero unit application"]
theorem h0Unit_apply (φ : R →+* S) (f : ι → R)
    (M : ModuleCat.{max u v} R) (m : M) :
    (h0Unit φ f M m).1 = h0UnitAmbient φ f M m := sorry

/-- The map on `H⁰(Can(-))` induced by a source-module morphism. -/
@[stacks 05EL "canonical formal gluing degree-zero map",
  stacks 05EM "canonical formal gluing degree-zero map"]
noncomputable def h0OfModuleMap (φ : R →+* S) (f : ι → R)
    {M N : ModuleCat.{max u v} R} (ψ : M ⟶ N) :
    (ofModule φ f M).h0Object ⟶ (ofModule φ f N).h0Object :=
  ModuleCat.ofHom (h0Map (ofModuleMap φ f ψ))

/-- The map on `H⁰(Can(-))` induced by an identity is the identity. -/
@[stacks 05EL "canonical formal gluing degree-zero map identity",
  stacks 05EM "canonical formal gluing degree-zero map identity"]
theorem h0OfModuleMap_id (φ : R →+* S) (f : ι → R)
    (M : ModuleCat.{max u v} R) :
    h0OfModuleMap φ f (𝟙 M) = 𝟙 (ofModule φ f M).h0Object := sorry

/-- The map on `H⁰(Can(-))` preserves composition. -/
@[stacks 05EL "canonical formal gluing degree-zero map composition",
  stacks 05EM "canonical formal gluing degree-zero map composition"]
theorem h0OfModuleMap_comp (φ : R →+* S) (f : ι → R)
    {M N P : ModuleCat.{max u v} R} (ψ : M ⟶ N) (χ : N ⟶ P) :
    h0OfModuleMap φ f (ψ ≫ χ) =
      h0OfModuleMap φ f ψ ≫ h0OfModuleMap φ f χ := sorry

/-- Canonical formal gluing followed by degree-zero sections, with its map
written through the explicit `h0Map` and `ofModuleMap` owners. -/
@[stacks 05EL "canonical formal gluing degree-zero composite functor",
  stacks 05EM "canonical formal gluing degree-zero composite functor"]
noncomputable def h0OfModuleFunctor (φ : R →+* S) (f : ι → R) :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj M := (ofModule φ f M).h0Object
  map ψ := h0OfModuleMap φ f ψ
  map_id := h0OfModuleMap_id φ f
  map_comp := h0OfModuleMap_comp φ f

/-- The explicit `H⁰(Can(-))` functor is the categorical composite of the
two canonical functors. -/
@[stacks 05EL "canonical formal gluing degree-zero functor comparison",
  stacks 05EM "canonical formal gluing degree-zero functor comparison"]
theorem h0OfModuleFunctor_eq_comp (φ : R →+* S) (f : ι → R) :
    h0OfModuleFunctor φ f =
      ofModuleFunctor φ f ⋙ h0Functor (φ := φ) (f := f) := sorry

/-- The canonical degree-zero unit as a morphism between the source module
and the explicit `H⁰(Can(-))` functor value. -/
@[stacks 05EL "canonical formal gluing degree-zero unit morphism",
  stacks 05EM "canonical formal gluing degree-zero unit morphism"]
noncomputable def h0UnitHom (φ : R →+* S) (f : ι → R)
    (M : ModuleCat.{max u v} R) :
    (𝟭 (ModuleCat.{max u v} R)).obj M ⟶
      (h0OfModuleFunctor φ f).obj M :=
  ModuleCat.ofHom (h0Unit φ f M)

/-- The degree-zero unit commutes with source-module morphisms. -/
@[stacks 05EL "canonical formal gluing degree-zero unit naturality",
  stacks 05EM "canonical formal gluing degree-zero unit naturality"]
theorem h0Unit_naturality (φ : R →+* S) (f : ι → R)
    {M N : ModuleCat.{max u v} R} (ψ : M ⟶ N) :
    (𝟭 (ModuleCat.{max u v} R)).map ψ ≫ h0UnitHom φ f N =
      h0UnitHom φ f M ≫
        (h0OfModuleFunctor φ f).map ψ := sorry

/-- The units `M → H⁰(Can(M))`, assembled into a natural transformation. -/
@[stacks 05EL "canonical formal gluing degree-zero unit transformation",
  stacks 05EM "canonical formal gluing degree-zero unit transformation"]
noncomputable def h0UnitNatTrans (φ : R →+* S) (f : ι → R) :
    𝟭 (ModuleCat.{max u v} R) ⟶
      h0OfModuleFunctor φ f where
  app M := h0UnitHom φ f M
  naturality := fun {M N} ψ ↦
    h0Unit_naturality (M := M) (N := N) φ f ψ

/-- For a finite principal-open family, flatness and bijectivity on the
quotient by the cover ideal make the degree-zero unit bijective. -/
@[stacks 05EM "flat formal gluing degree-zero recovery"]
theorem h0Unit_bijective_of_flat_of_quotientMap_bijective [Finite ι]
    (φ : R →+* S) (f : ι → R) (hflat : φ.Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map))
    (M : ModuleCat.{max u v} R) :
    Function.Bijective (h0Unit φ f M) := sorry

/-- The linear equivalence supplied by degree-zero recovery under the flat
quotient hypotheses.  Its forward map is the explicit `h0Unit`. -/
@[stacks 05EM "flat formal gluing degree-zero recovery equivalence"]
noncomputable def h0UnitEquiv_of_flat_of_quotientMap_bijective [Finite ι]
    (φ : R →+* S) (f : ι → R) (hflat : φ.Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map))
    (M : ModuleCat.{max u v} R) :
    M ≃ₗ[R] (ofModule φ f M).h0Module :=
  LinearEquiv.ofBijective (h0Unit φ f M)
    (h0Unit_bijective_of_flat_of_quotientMap_bijective
      φ f hflat hquot M)

/-- The forward map of the recovery equivalence is the canonical
degree-zero unit. -/
@[simp, stacks 05EM "flat formal gluing recovery equivalence map"]
theorem h0UnitEquiv_toLinearMap [Finite ι]
    (φ : R →+* S) (f : ι → R) (hflat : φ.Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map))
    (M : ModuleCat.{max u v} R) :
    (h0UnitEquiv_of_flat_of_quotientMap_bijective
      φ f hflat hquot M).toLinearMap = h0Unit φ f M := sorry

/-- The componentwise recovery equivalence as an isomorphism in
`ModuleCat R`. -/
@[stacks 05EM "flat formal gluing degree-zero recovery module isomorphism"]
noncomputable def h0UnitIso_of_flat_of_quotientMap_bijective [Finite ι]
    (φ : R →+* S) (f : ι → R) (hflat : φ.Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map))
    (M : ModuleCat.{max u v} R) :
    (𝟭 (ModuleCat.{max u v} R)).obj M ≅
      (h0OfModuleFunctor φ f).obj M :=
  (h0UnitEquiv_of_flat_of_quotientMap_bijective
    φ f hflat hquot M).toModuleIso

/-- The componentwise recovery isomorphisms are natural in the source
module. -/
@[stacks 05EM "flat formal gluing recovery isomorphism naturality"]
theorem h0UnitIso_naturality [Finite ι]
    (φ : R →+* S) (f : ι → R) (hflat : φ.Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map))
    {M N : ModuleCat.{max u v} R} (ψ : M ⟶ N) :
    (𝟭 (ModuleCat.{max u v} R)).map ψ ≫
        (h0UnitIso_of_flat_of_quotientMap_bijective
          φ f hflat hquot N).hom =
      (h0UnitIso_of_flat_of_quotientMap_bijective
          φ f hflat hquot M).hom ≫
        (h0OfModuleFunctor φ f).map ψ := sorry

/-- The degree-zero unit is a natural isomorphism under the flat quotient
hypotheses. -/
@[stacks 05EM "flat formal gluing degree-zero unit isomorphism"]
noncomputable def h0UnitNatIso_of_flat_of_quotientMap_bijective [Finite ι]
    (φ : R →+* S) (f : ι → R) (hflat : φ.Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map)) :
    𝟭 (ModuleCat.{max u v} R) ≅ h0OfModuleFunctor φ f :=
  NatIso.ofComponents
    (h0UnitIso_of_flat_of_quotientMap_bijective
      φ f hflat hquot)
    (naturality := fun {M N} ψ ↦
      h0UnitIso_naturality (M := M) (N := N)
        φ f hflat hquot ψ)

/-- The forward component of the degree-zero unit natural isomorphism is the
explicit unit map. -/
@[simp, stacks 05EM "flat formal gluing degree-zero unit isomorphism component"]
theorem h0UnitNatIso_hom_app [Finite ι]
    (φ : R →+* S) (f : ι → R) (hflat : φ.Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map))
    (M : ModuleCat.{max u v} R) :
    (h0UnitNatIso_of_flat_of_quotientMap_bijective
      φ f hflat hquot).hom.app M =
        h0UnitHom φ f M := sorry

/-- Transporting the explicit degree-zero unit isomorphism across the
functor comparison gives the literal `𝟭 ≅ Can ⋙ H⁰` statement. -/
@[stacks 05EM "flat formal gluing composite unit isomorphism"]
noncomputable def h0UnitCompNatIso_of_flat_of_quotientMap_bijective
    [Finite ι] (φ : R →+* S) (f : ι → R) (hflat : φ.Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map)) :
    𝟭 (ModuleCat.{max u v} R) ≅
      ofModuleFunctor φ f ⋙ h0Functor (φ := φ) (f := f) :=
  h0UnitNatIso_of_flat_of_quotientMap_bijective
      φ f hflat hquot ≪≫
    eqToIso (h0OfModuleFunctor_eq_comp φ f)

/-- Lemma 15.90.12: for a finite principal-open family, a flat ring map
whose quotient map along the cover ideal is bijective makes `H⁰` a left
quasi-inverse to canonical formal gluing. -/
@[stacks 05EM "formal gluing degree-zero left quasi-inverse"]
noncomputable def h0LeftQuasiInverseIso_of_flat_of_quotientMap_bijective
    [Finite ι] (φ : R →+* S) (f : ι → R) (hflat : φ.Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map)) :
    ofModuleFunctor φ f ⋙ h0Functor (φ := φ) (f := f) ≅
      𝟭 (ModuleCat.{max u v} R) :=
  (h0UnitCompNatIso_of_flat_of_quotientMap_bijective
    φ f hflat hquot).symm

end LocalizedModule.Away.FormalGluing
