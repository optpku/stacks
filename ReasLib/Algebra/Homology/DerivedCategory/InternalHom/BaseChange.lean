/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Pushout
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Pushout
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Restriction
public import ReasLib.RingTheory.Finiteness.Projective.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of canonical derived Hom models

The arbitrary ring-map theorem takes explicit identifications of the scalar-extended input models;
this is the representation-independent core.  Its pushout specialization derives those
identifications from bounded relative flatness and keeps the source ring square visible.  The
conclusions target the canonical `InternalHom.RHom.obj`; comparison with a selected ambient closed
structure belongs to the optional compatibility leaf.  Like the underlying scalar-extension model
owners, these source-facing comparisons currently use the standard same-universe module-category
presentation; the canonical `RHom` object itself is more general. Each comparison retains
the existing canonical `RHom` availability of its target coefficient ring.

@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace CochainComplex.HomComplex

variable {A B : Type u} [CommRing A] [CommRing B]

namespace ScalarExtension

variable [hasRHom : CategoryTheory.DerivedCategory.InternalHom.RHom.Has.{u, u} (A := B)]

/-- Lemma 15.85.6 (Stacks `0E1U`): scalar extension of a finite-projective Hom model represents
canonical target-ring `RHom` after explicit identifications of the scalar-extended inputs. -/
@[stacks 0E1U "scalar extension of a canonical RHom model"]
theorem representsRHom
    (σ : A →+* B)
    {K L : DerivedCategory (ModuleCat.{u} B)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj P) ≅ K)
    (eF : DerivedCategory.Q.obj ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj F) ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj
          (CochainComplex.HomComplex.moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := B) K L) := by
  letI : Algebra A B := σ.toAlgebra
  have hPminus : CochainComplex.minus (ModuleCat B)
      ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj P) :=
    CochainComplex.minus_map (ModuleCat.extendScalars σ) hP
  have hPfp' :
      ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj P).IsTermwiseFiniteProjective := by
    intro i
    change Module.FiniteProjective B (B ⊗[A] (P.X i : Type u))
    exact Module.FiniteProjective.baseChange (hPfp i)
  rcases CochainComplex.ProjectiveMinus.representsRHom_of_models
      ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj P)
      ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj F)
      eP eF hPminus hPfp' with ⟨e⟩
  exact ⟨DerivedCategory.Q.mapIso
    (CochainComplex.HomComplex.ScalarExtension.comparisonIso_of_finiteProjective
      σ P F hP hPfp hF) ≪≫ e⟩

/-- Source-facing compatibility name for the scalar-extension comparison. -/
@[stacks 0E1U "scalar extension of an internal-Hom model"]
abbrev representsInternalHom
    (σ : A →+* B) {K L : DerivedCategory (ModuleCat.{u} B)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj P) ≅ K)
    (eF : DerivedCategory.Q.obj ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj F) ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj
          (CochainComplex.HomComplex.moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := B) K L) :=
  representsRHom σ P F eP eF hP hPfp hF
/- Proof strategy: transport `hP` and `hF` with `CochainComplex.minus_map` and
`CochainComplex.plus_map`, use the finite-projective scalar-extension instances degreewise, then
apply `CochainComplex.HomComplex.ScalarExtension.comparison_isIso` and transport
`CochainComplex.ProjectiveMinus.representsRHom` through `eP` and `eF`. -/

end ScalarExtension

namespace DerivedExtension

variable [hasRHom : CategoryTheory.DerivedCategory.InternalHom.RHom.Has.{u, u} (A := B)]

/-- Lemma 15.85.6 (Stacks `0E1U`): for an arbitrary ring map, a finite-projective source model and
a target model on which the derived-extension counit is invertible give a scalar-extended model of
canonical derived `RHom`. -/
@[stacks 0E1U "canonical RHom model after derived scalar extension"]
theorem representsRHom
    (σ : A →+* B)
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F)
    (hFσ : IsIso ((ModuleCat.derivedExtensionComplexCounit σ).app F)) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj
          (CochainComplex.HomComplex.moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := B)
        ((ModuleCat.derivedExtensionOfScalars σ).obj K)
        ((ModuleCat.derivedExtensionOfScalars σ).obj L)) := by
  let eP' : DerivedCategory.Q.obj
        ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj P) ≅
      (ModuleCat.derivedExtensionOfScalars σ).obj K :=
    (ModuleCat.DerivedExtension.BoundedAbove.counitIso_of_isTermwiseFiniteProjective
      σ P hP hPfp).symm ≪≫
      (ModuleCat.derivedExtensionOfScalars σ).mapIso eP
  let eF' : DerivedCategory.Q.obj
        ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj F) ≅
      (ModuleCat.derivedExtensionOfScalars σ).obj L :=
    (ModuleCat.DerivedExtension.counitIso σ F hFσ).symm ≪≫
      (ModuleCat.derivedExtensionOfScalars σ).mapIso eF
  exact ScalarExtension.representsRHom σ P F eP' eF' hP hPfp hF

/-- Source-facing compatibility name for the derived-extension comparison. -/
@[stacks 0E1U "internal-Hom model after derived scalar extension"]
abbrev representsInternalHom
    (σ : A →+* B) {K L : DerivedCategory (ModuleCat.{u} A)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F)
    (hFσ : IsIso ((ModuleCat.derivedExtensionComplexCounit σ).app F)) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        ((CochainComplex.HomComplex.ScalarExtension.functor σ).obj
          (CochainComplex.HomComplex.moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := B)
        ((ModuleCat.derivedExtensionOfScalars σ).obj K)
        ((ModuleCat.derivedExtensionOfScalars σ).obj L)) :=
  representsRHom σ P F eP eF hP hPfp hF hFσ
/- Proof strategy: use the named counit isomorphism `hFσ` to establish the derived-extension
comparison for `F`, invoke the scalar-extension model theorem, and compose with that comparison. -/

end DerivedExtension

namespace Pushout

variable {R A R' A' : Type u}
variable [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
variable [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
variable [IsScalarTower R A A'] [IsScalarTower R R' A']
variable [hpush : Algebra.IsPushout R R' A A']
variable [Module.Flat R A]
variable [hasRHom : CategoryTheory.DerivedCategory.InternalHom.RHom.Has.{u, u} (A := A')]

include hpush

/-- Lemma 15.85.6 (Stacks `0E1U`): across a pushout of rings, a bounded relatively flat target and
a bounded-above finite-projective source give a scalar-extended model of canonical derived `RHom`.
-/
@[stacks 0E1U "relatively flat canonical RHom model after pushout"]
theorem representsRHom
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hFminus : CochainComplex.minus (ModuleCat A) F)
    (hFplus : CochainComplex.plus (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (CategoryTheory.ModuleCat.Pushout.algebraBaseChange
          (A := A) (A' := A')
          (CochainComplex.HomComplex.moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A')
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K)
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj L)) :=
  DerivedExtension.representsRHom (algebraMap A A') P F eP eF hP hPfp hFplus
    (CategoryTheory.ModuleCat.Pushout.DerivedExtension.counitIsIso
      (R' := R') F hFminus hFflat)
/- Proof strategy: specialize `DerivedExtension.representsRHom` to `algebraMap A A'`;
the pushout owner supplies the named derived-extension counit theorem, and the relative flatness
hypotheses provide the target model bounds. -/

/-- Lemma 15.85.6 (Stacks `0E1U`): the bounded-model specialization of the pushout internal-Hom comparison. -/
@[stacks 0E1U "bounded relatively flat canonical RHom model after pushout"]
theorem representsRHom_of_bounded
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K)
    (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.bounded (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (CategoryTheory.ModuleCat.Pushout.algebraBaseChange
          (A := A) (A' := A')
          (CochainComplex.HomComplex.moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A')
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K)
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj L)) := by
  obtain ⟨hFplus, hFminus⟩ := (CochainComplex.bounded_iff (ModuleCat A) F).mp hF
  exact representsRHom (R' := R') P F eP eF hP hPfp hFminus hFplus hFflat
/- Proof strategy: obtain `hFminus` and `hFplus` from
`(CochainComplex.bounded_iff (ModuleCat A) F).mp hF`, then call
`Pushout.representsRHom` with the same finite-projective source and flatness witness. -/

/-- Source-facing compatibility name for the pushout comparison. -/
@[stacks 0E1U "relatively flat internal-Hom model after pushout"]
abbrev representsInternalHom
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfp : P.IsTermwiseFiniteProjective)
    (hFminus : CochainComplex.minus (ModuleCat A) F)
    (hFplus : CochainComplex.plus (ModuleCat A) F) (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (CategoryTheory.ModuleCat.Pushout.algebraBaseChange
          (A := A) (A' := A') (CochainComplex.HomComplex.moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A')
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K)
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj L)) :=
  representsRHom (R' := R') P F eP eF hP hPfp hFminus hFplus hFflat

/-- Source-facing compatibility name for the bounded pushout comparison. -/
@[stacks 0E1U "bounded relatively flat internal-Hom model after pushout"]
abbrev representsInternalHom_of_bounded
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.bounded (ModuleCat A) F) (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (CategoryTheory.ModuleCat.Pushout.algebraBaseChange
          (A := A) (A' := A') (CochainComplex.HomComplex.moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A')
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K)
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj L)) :=
  representsRHom_of_bounded (R' := R') P F eP eF hP hPfp hF hFflat

end Pushout

end CochainComplex.HomComplex
