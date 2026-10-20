/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Acyclic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localization of Bounded Homotopy Categories

@stack 0159
@stack 05RW

This module owns the canonical functors from `K⁺(A)`, `K⁻(A)`, and `Kᵇ(A)` to the corresponding
bounded derived categories. It computes their kernels and registers the localization structures.
The denominator and acyclic object properties themselves live one layer lower in
`HomotopyCategory.QuasiIso.Bounded`.
-/

open CategoryTheory.Limits CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty
open ComplexShape DerivedCategory.TStructure
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

namespace DerivedCategory.Plus

/-- The bounded-below cochain localization preserves addition of morphisms. -/
@[stacks 0159 "bounded-below derived localization is additive"]
noncomputable instance Q.additive :
    (_root_.DerivedCategory.Plus.Q :
      CochainComplex.Plus 𝒜 ⥤ _root_.DerivedCategory.Plus 𝒜).Additive := sorry

/-- The ambient localization sends bounded-below homotopy objects to bounded-below derived
objects. -/
theorem Qh.object_mem (X : HomotopyCategory.Plus 𝒜) :
    (t.plus : ObjectProperty (DerivedCategory 𝒜)) (DerivedCategory.Qh.obj X.obj) := sorry

/-- A chosen cochain representative of a bounded-below derived object has vanishing homology in
sufficiently negative degrees. -/
theorem Representative.homology_eventually_zero (X : DerivedCategory.Plus 𝒜) :
    ∃ a : ℤ, ∀ i < a, IsZero ((DerivedCategory.Q.objPreimage X.obj).homology i) := sorry

/-- After inclusion into the ambient derived category, the bounded-below
localization agrees with the ordinary derived localization of the underlying complex. -/
@[stacks 0159]
noncomputable def Qh.compInclusionIso (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] :
    ((DerivedCategory.Plus.Q : CochainComplex.Plus 𝒜 ⥤ DerivedCategory.Plus 𝒜) ⋙
      (DerivedCategory.Plus.ι : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory 𝒜)) ≅
      CochainComplex.Plus.ι 𝒜 ⋙
        (DerivedCategory.Q : CochainComplex 𝒜 ℤ ⥤ DerivedCategory 𝒜) :=
  Functor.associator
      (HomotopyCategory.Plus.quotient 𝒜)
      (DerivedCategory.Plus.Qh : HomotopyCategory.Plus 𝒜 ⥤ DerivedCategory.Plus 𝒜)
      (DerivedCategory.Plus.ι : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory 𝒜) ≪≫
    Functor.isoWhiskerLeft
      (HomotopyCategory.Plus.quotient 𝒜)
      (DerivedCategory.Plus.QhCompιIsoιCompQh 𝒜) ≪≫
    Functor.associator
      (HomotopyCategory.Plus.quotient 𝒜)
      (HomotopyCategory.Plus.ι 𝒜)
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      (HomotopyCategory.Plus.quotientCompιIso 𝒜)
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft
      (CochainComplex.Plus.ι 𝒜)
      (DerivedCategory.quotientCompQhIso 𝒜)

/-- The kernel of `K⁺(A) ⥤ D⁺(A)` is the bounded-below acyclic object
property. -/
@[stacks 05RW "kernel of bounded-below derived localization"]
theorem Qh.kernel_eq_acyclic :
    Functor.kernel
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus 𝒜 ⥤ DerivedCategory.Plus 𝒜) =
      HomotopyCategory.Plus.acyclic 𝒜 := sorry

/-- Every bounded-below derived object is represented by a bounded-below homotopy object. -/
theorem Qh.essSurj :
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus 𝒜 ⥤ DerivedCategory.Plus 𝒜).EssSurj := sorry

end DerivedCategory.Plus

namespace DerivedCategory.Minus

/-- The ambient localization sends bounded-above homotopy objects to bounded-above derived
objects. -/
theorem Qh.object_mem (X : HomotopyCategory.Minus 𝒜) :
    (t.minus : ObjectProperty (DerivedCategory 𝒜)) (DerivedCategory.Qh.obj X.obj) := by
  obtain ⟨bound, boundInstance⟩ := X.property
  exact ⟨bound, t.isLE_of_iso
    ((DerivedCategory.quotientCompQhIso 𝒜).symm.app X.obj.as) bound⟩

/-- A chosen cochain representative of a bounded-above derived object has vanishing homology in
sufficiently positive degrees. -/
theorem Representative.homology_eventually_zero (X : DerivedCategory.Minus 𝒜) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.Q.objPreimage X.obj).homology i) := by
  obtain ⟨bound, boundInstance⟩ := X.property
  have representativeBound :
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X.obj)).IsLE bound :=
    t.isLE_of_iso (DerivedCategory.Q.objObjPreimageIso X.obj).symm bound
  have complexBound := (DerivedCategory.isLE_Q_obj_iff _ bound).mp representativeBound
  refine ⟨bound, fun degree inequality => ?_⟩
  exact ((DerivedCategory.Q.objPreimage X.obj).exactAt_of_isLE
    bound degree inequality).isZero_homology

/-- The canonical localization functor `K⁻(A) ⥤ D⁻(A)`. -/
@[stacks 05RW "bounded-above derived localization functor"]
noncomputable def Qh (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] :
    HomotopyCategory.Minus 𝒜 ⥤ DerivedCategory.Minus 𝒜 :=
  (t.minus : ObjectProperty (DerivedCategory 𝒜)).lift
    ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh) Qh.object_mem

/-- The bounded-above localization functor commutes with cohomological shifts. -/
noncomputable instance Qh.commShift : (Qh 𝒜).CommShift ℤ := by
  dsimp only [Qh]
  infer_instance

/-- The bounded-above localization functor is exact. -/
instance Qh.isTriangulated : (Qh 𝒜).IsTriangulated := sorry

/-- Composing `Qh` with the bounded-above inclusion recovers the ambient localization. -/
noncomputable def Qh.compInclusionIso (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] :
    Qh 𝒜 ⋙ DerivedCategory.Minus.ι ≅
      (HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh :=
  Iso.refl _

/-- Every bounded-above derived object is represented by a bounded-above homotopy object. -/
theorem Qh.essSurj : (Qh 𝒜).EssSurj where
  mem_essImage := by
    rintro ⟨object, bound, complex, comparison, complexBound⟩
    refine ⟨⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj complex,
      ⟨bound, complexBound⟩⟩, ⟨?_⟩⟩
    exact DerivedCategory.Minus.ι.preimageIso
      ((DerivedCategory.quotientCompQhIso 𝒜).app complex ≪≫ comparison.symm)

/-- `D⁻(A)` is the localization of `K⁻(A)` at bounded-above
quasi-isomorphisms. -/
@[stacks 05RW "bounded-above derived localization"]
instance Qh.isLocalization :
    (Qh 𝒜).IsLocalization (HomotopyCategory.Minus.quasiIso 𝒜) := by
  have leftLocalizing : (HomotopyCategory.minus 𝒜).IsVerdierLeftLocalizing
      (HomotopyCategory.subcategoryAcyclic 𝒜) :=
    { fac := by
        intro source target morphism sourceBound targetAcyclic
        obtain ⟨source : CochainComplex 𝒜 ℤ, rfl⟩ :=
          HomotopyCategory.quotient_obj_surjective source
        obtain ⟨target : CochainComplex 𝒜 ℤ, rfl⟩ :=
          HomotopyCategory.quotient_obj_surjective target
        change CochainComplex.minus 𝒜 source at sourceBound
        obtain ⟨bound, boundInstance⟩ := sourceBound
        obtain ⟨morphism, rfl⟩ :=
          (HomotopyCategory.quotient 𝒜 (up ℤ)).map_surjective morphism
        rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
          at targetAcyclic
        refine ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (target.truncLE bound),
          (HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (inv (source.ιTruncLE bound) ≫ CochainComplex.truncLEMap morphism bound),
          (HomotopyCategory.quotient 𝒜 (up ℤ)).map (target.ιTruncLE bound),
          ⟨bound, by
            change (target.truncLE bound).IsStrictlyLE bound
            infer_instance⟩, ?_, ?_⟩
        · rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
          exact targetAcyclic.truncLE _
        · simp [← Functor.map_comp, Category.assoc,
            CochainComplex.ιTruncLE_naturality] }
  have essentiallySurjective := Qh.essSurj (𝒜 := 𝒜)
  rw [← HomotopyCategory.Minus.acyclic_trW_eq_quasiIso 𝒜]
  exact ((HomotopyCategory.minus 𝒜).triangulatedLocalizerMorphism
    (HomotopyCategory.subcategoryAcyclic 𝒜)).isLocalization_of_isLocalizedFullyFaithful
      (Qh.compInclusionIso 𝒜).symm

/-- The kernel of `K⁻(A) ⥤ D⁻(A)` is the bounded-above acyclic object
property. -/
@[stacks 05RW "kernel of bounded-above derived localization"]
theorem Qh.kernel_eq_acyclic :
    Functor.kernel (Qh 𝒜) = HomotopyCategory.Minus.acyclic 𝒜 := sorry

end DerivedCategory.Minus

namespace DerivedCategory.Bounded

/-- The ambient localization sends bounded homotopy objects to bounded derived objects. -/
theorem Qh.object_mem (X : HomotopyCategory.Bounded 𝒜) :
    (t.bounded : ObjectProperty (DerivedCategory 𝒜)) (DerivedCategory.Qh.obj X.obj) := sorry

/-- A chosen cochain representative of a bounded derived object has homology supported in a
finite interval. -/
@[stacks 05RW "bounded representative has finite-range homology"]
theorem Representative.homology_eventually_zero (X : DerivedCategory.Bounded 𝒜) :
    ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.Q.objPreimage X.obj).homology i) := sorry

/-- The canonical localization functor `Kᵇ(A) ⥤ Dᵇ(A)`. -/
@[stacks 05RW "bounded derived localization functor"]
noncomputable def Qh (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] :
    HomotopyCategory.Bounded 𝒜 ⥤ DerivedCategory.Bounded 𝒜 :=
  (t.bounded : ObjectProperty (DerivedCategory 𝒜)).lift
    ((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh) Qh.object_mem

/-- The bounded localization functor commutes with cohomological shifts. -/
noncomputable instance Qh.commShift : (Qh 𝒜).CommShift ℤ := by
  dsimp only [Qh]
  infer_instance

/-- The bounded localization functor is exact. -/
instance Qh.isTriangulated : (Qh 𝒜).IsTriangulated := sorry

/-- Composing `Qh` with the bounded inclusion recovers the ambient localization. -/
noncomputable def Qh.compInclusionIso (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] :
    Qh 𝒜 ⋙ DerivedCategory.Bounded.ι ≅
      (HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh :=
  Iso.refl _

/-- Every bounded derived object is represented by a bounded homotopy object. -/
theorem Qh.essSurj : (Qh 𝒜).EssSurj := sorry

/-- `Dᵇ(A)` is the localization of `Kᵇ(A)` at bounded
quasi-isomorphisms. -/
@[stacks 05RW "bounded derived localization"]
instance Qh.isLocalization :
    (Qh 𝒜).IsLocalization
      ((HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
        (HomotopyCategory.bounded 𝒜).ι) := sorry

/-- The kernel of `Kᵇ(A) ⥤ Dᵇ(A)` is the bounded acyclic object property. -/
@[stacks 05RW "kernel of bounded derived localization"]
theorem Qh.kernel_eq_acyclic :
    Functor.kernel (Qh 𝒜) = HomotopyCategory.Bounded.acyclic 𝒜 := sorry

end DerivedCategory.Bounded

end CategoryTheory
