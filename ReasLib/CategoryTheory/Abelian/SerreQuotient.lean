/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Functor.Exactness.Faithful
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Serre Quotients of Abelian Categories

This file equips the canonical localization at a Serre class with its coherent abelian-category
instance, bundles the inclusion and quotient as exact functors, and exposes the factorization and
homology interfaces used by downstream consumers.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe uA vA uB vB

namespace CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

/-- The canonical Serre localization carries its coherent abelian-category structure. -/
@[stacks 02MS]
noncomputable instance instAbelianLocalization :
    Abelian P.isoModSerre.Localization :=
  abelian P.isoModSerre.Q P

/-- The canonical Serre quotient preserves finite limits.  This is a global owner instance so
downstream derived-category constructions do not need to rebuild the exactness data locally. -/
@[stacks 02MS]
noncomputable instance quotient_preservesFiniteLimits :
    PreservesFiniteLimits P.isoModSerre.Q :=
  preservesFiniteLimits P.isoModSerre.Q P

/-- The canonical Serre quotient preserves finite colimits.  Together with
`quotient_preservesFiniteLimits`, this is the canonical exactness interface for the quotient. -/
@[stacks 02MS]
noncomputable instance quotient_preservesFiniteColimits :
    PreservesFiniteColimits P.isoModSerre.Q :=
  preservesFiniteColimits P.isoModSerre.Q P

/-- The canonical Serre quotient functor is essentially surjective. -/
@[stacks 02MS]
noncomputable instance instEssSurjQuotientFunctor : P.isoModSerre.Q.EssSurj :=
  Localization.essSurj P.isoModSerre.Q P.isoModSerre

/-- The inclusion of the Serre full subcategory, bundled as an exact functor. -/
@[stacks 02MS]
def inclusionExactFunctor : P.FullSubcategory ⥤ₑ A :=
  ⟨P.ι, IsWeakSerreClass.Inclusion.isExact P⟩

/-- The canonical localization functor is exact. -/
@[stacks 02MS]
theorem quotient_exact :
    exactFunctor A P.isoModSerre.Localization P.isoModSerre.Q := sorry

/-- The canonical localization functor, bundled as an exact functor. -/
@[stacks 02MS]
def quotientExactFunctor : A ⥤ₑ P.isoModSerre.Localization :=
  ⟨P.isoModSerre.Q, quotient_exact P⟩

/-- The exact inclusion has the original full-subcategory inclusion as its underlying functor. -/
@[stacks 02MS "underlying object of the exact Serre inclusion", simp]
theorem inclusionExactFunctor_obj (X : P.FullSubcategory) :
    (inclusionExactFunctor P).obj.obj X = X.1 := sorry

/-- The exact inclusion acts on maps by the original full-subcategory morphism. -/
@[stacks 02MS "underlying map of the exact Serre inclusion", simp]
theorem inclusionExactFunctor_map {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    (inclusionExactFunctor P).obj.map f = P.ι.map f := sorry

/-- The exact quotient has the canonical localization as its underlying functor. -/
@[stacks 02MS "underlying object of the exact Serre quotient", simp]
theorem quotientExactFunctor_obj (X : A) :
    (quotientExactFunctor P).obj.obj X = P.isoModSerre.Q.obj X := sorry

/-- The exact quotient acts on maps by the canonical localization functor. -/
@[stacks 02MS "underlying map of the exact Serre quotient", simp]
theorem quotientExactFunctor_map {X Y : A} (f : X ⟶ Y) :
    (quotientExactFunctor P).obj.map f = P.isoModSerre.Q.map f := sorry

/-- The kernel of the canonical Serre quotient functor is the original Serre class. -/
@[stacks 02MS]
theorem quotientKernel_eq : (quotientExactFunctor P).obj.kernel = P := sorry

/-- An exact functor factors through the Serre quotient exactly when its kernel contains the
Serre class. -/
@[stacks 02MS]
theorem exactFunctor_mem_essImage_iff
    {B : Type uB} [Category.{vB} B] [Abelian B] (G : A ⥤ₑ B) :
    (whiskeringLeft P.isoModSerre.Q P B).essImage G ↔
      P ≤ G.obj.kernel := sorry

/-- The functor induced on the Serre quotient by an exact functor whose kernel contains the
Serre class. -/
@[stacks 06XK]
def inducedFunctor
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel) :
    P.isoModSerre.Localization ⥤ B :=
  Localization.lift G.obj
    ((P.isoModSerre_isInvertedBy_iff G.obj).2 hPker) P.isoModSerre.Q

/-- The functor induced on a Serre quotient by an exact functor is exact. -/
theorem inducedFunctor_exact
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel) :
    exactFunctor P.isoModSerre.Localization B (inducedFunctor P G hPker) := by
  rw [← exactFunctor_comp_iff P.isoModSerre.Q P]
  exact ObjectProperty.prop_of_iso _
    (Localization.fac G.obj
      ((P.isoModSerre_isInvertedBy_iff G.obj).2 hPker) P.isoModSerre.Q).symm G.property

/-- The induced functor on the Serre quotient preserves finite limits. -/
noncomputable instance inducedFunctor_preservesFiniteLimits
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel) :
    PreservesFiniteLimits (inducedFunctor P G hPker) :=
  (exactFunctor_iff (inducedFunctor P G hPker)).1 (inducedFunctor_exact P G hPker) |>.1

/-- The induced functor on the Serre quotient preserves finite colimits. -/
noncomputable instance inducedFunctor_preservesFiniteColimits
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel) :
    PreservesFiniteColimits (inducedFunctor P G hPker) :=
  (exactFunctor_iff (inducedFunctor P G hPker)).1 (inducedFunctor_exact P G hPker) |>.2

/-- The exact functor induced on the Serre quotient, bundled for downstream composition. -/
@[stacks 06XK]
def inducedExactFunctor
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel) :
    P.isoModSerre.Localization ⥤ₑ B :=
  ⟨inducedFunctor P G hPker, inducedFunctor_exact P G hPker⟩

/-- The underlying object of the induced exact functor is given by `inducedFunctor`. -/
@[stacks 06XK, simp]
theorem inducedExactFunctor_obj
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel)
    (X : P.isoModSerre.Localization) :
    (inducedExactFunctor P G hPker).obj.obj X = (inducedFunctor P G hPker).obj X := sorry

/-- The underlying map of the induced exact functor is given by `inducedFunctor`. -/
@[stacks 06XK, simp]
theorem inducedExactFunctor_map
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel)
    {X Y : P.isoModSerre.Localization} (f : X ⟶ Y) :
    (inducedExactFunctor P G hPker).obj.map f = (inducedFunctor P G hPker).map f := sorry

/-- An exact functor has exactly the prescribed Serre kernel if and only if the induced functor
on the Serre quotient is faithful. -/
@[stacks 06XK]
theorem kernel_eq_iff_inducedFunctor_faithful
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel) :
    P = G.obj.kernel ↔ (inducedFunctor P G hPker).Faithful := by
  constructor
  · intro hker
    exact Functor.faithful_of_exact_of_kernel_le_isZero (inducedFunctor P G hPker) <|
      fun Y hY ↦ by
        have hpre :
            IsZero ((inducedFunctor P G hPker).obj
              (P.isoModSerre.Q.obj (P.isoModSerre.Q.objPreimage Y))) := by
          simpa using
            (((inducedFunctor P G hPker).mapIso
              (P.isoModSerre.Q.objObjPreimageIso Y)).isZero_iff).2 hY
        have hkernel : G.obj.kernel (P.isoModSerre.Q.objPreimage Y) := by
          simpa [inducedFunctor] using
            ((Localization.fac G.obj
              ((P.isoModSerre_isInvertedBy_iff G.obj).2 hPker)
              P.isoModSerre.Q).app (P.isoModSerre.Q.objPreimage Y)).isZero_iff.1 hpre
        have hPpre : P (P.isoModSerre.Q.objPreimage Y) := by
          simpa [hker] using hkernel
        have hQpre : IsZero (P.isoModSerre.Q.obj (P.isoModSerre.Q.objPreimage Y)) :=
          (isZero_obj_iff P.isoModSerre.Q P _).2 hPpre
        exact (P.isoModSerre.Q.objObjPreimageIso Y).isZero_iff.1 hQpre
  · intro hfaithful
    ext X
    constructor
    · exact hPker X
    · intro hkernel
      have hQX : IsZero ((inducedFunctor P G hPker).obj (P.isoModSerre.Q.obj X)) := by
        simpa [inducedFunctor] using
          ((Localization.fac G.obj
            ((P.isoModSerre_isInvertedBy_iff G.obj).2 hPker)
            P.isoModSerre.Q).app X).isZero_iff.2 hkernel
      have hQid : 𝟙 (P.isoModSerre.Q.obj X) = 0 := by
        apply (Functor.map_injective (inducedFunctor P G hPker))
        simpa [IsZero.iff_id_eq_zero] using
          (show 𝟙 ((inducedFunctor P G hPker).obj (P.isoModSerre.Q.obj X)) = 0 from
            (IsZero.iff_id_eq_zero _).1 hQX)
      exact (isZero_obj_iff P.isoModSerre.Q P X).1 <|
        (IsZero.iff_id_eq_zero _).2 hQid

/-- If a localization of an abelian category sends a complex to an acyclic complex, then every
homology object of the original complex belongs to the localized Serre class. -/
@[stacks 02MX]
theorem mem_homology_of_map_acyclic
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (L : A ⥤ B) [L.IsLocalization P.isoModSerre] [L.Additive]
    {ι : Type*} {c : ComplexShape ι} {K : HomologicalComplex A c}
    (hK : ((L.mapHomologicalComplex c).obj K).Acyclic) (i : ι) :
    P (K.homology i) := sorry

/-- A homology object of a complex acyclic in the canonical Serre quotient, regarded as an object
of the Serre full subcategory. -/
@[stacks 02MX]
def acyclicHomology
    {ι : Type*} {c : ComplexShape ι} {K : HomologicalComplex A c}
    (hK : ((P.isoModSerre.Q.mapHomologicalComplex c).obj K).Acyclic)
    (i : ι) : P.FullSubcategory :=
  ⟨K.homology i,
    mem_homology_of_map_acyclic P P.isoModSerre.Q hK i⟩

/-- The underlying object of `acyclicHomology` is the corresponding homology object. -/
@[simp]
theorem acyclicHomology_obj
    {ι : Type*} {c : ComplexShape ι} {K : HomologicalComplex A c}
    (hK : ((P.isoModSerre.Q.mapHomologicalComplex c).obj K).Acyclic)
    (i : ι) :
    (acyclicHomology P hK i).1 = K.homology i := sorry

end CategoryTheory.ObjectProperty.SerreClassLocalization
