/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Complex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Monoidal
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal Hom from strictly perfect complexes

This leaf owns the ringed-site statements used by the Chapter 20 bridge.  The source complex is
expressed by the canonical `CochainComplex.IsStrictlyPerfect` property, and the target is the
canonical internal-Hom complex `(ihom E).obj F`; no chapter-specific notation or representative
choice is exposed.
-/

@[expose] public section

-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite (ringedSiteModuleCategory ringSheaf)
noncomputable section

-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe u v w

namespace RingedSite.CochainComplex.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {O : Sheaf J CommRingCat.{w}}

section Derived

variable [MonoidalClosed
  (CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)]
variable [RingedSite.Hom.ModuleDerived.KFlat.HomotopyTensorDescends O]
variable [RingedSite.Hom.ModuleDerived.KFlat.TensorDescends O]
variable [RingedSite.Hom.ModuleDerived.KFlat.IsLocalization O]

-- Fix the tensor before asking for its closed right-adjoint data. These are the exact
-- K-flat localization hypotheses, not an arbitrary monoidal structure on the derived category.
attribute [local instance] RingedSite.Hom.ModuleDerived.monoidalCategory
variable [MonoidalClosed
  (DerivedCategory (ringedSiteModuleCategory.{u, v, w, w} J O))]

/- The complex tensor is the canonical totalized tensor imported above. The derived tensor is
   the existing K-flat localization owner, with its three structural hypotheses explicit.
   Closedness supplies right-adjoint data for that exact tensor. No comparison or existence
   of the desired isomorphism is an input, and no deferred localization theorem selects data. -/

/-- Lemma 21.44.9 (08JH): a strictly perfect source computes derived internal Hom by the
canonical internal-Hom complex. -/
@[stacks 08JH "strictly perfect source computes derived internal Hom",
  stacks 08DM "strictly perfect internal-Hom complex represents derived internal Hom"]
theorem represents_of_strictlyPerfect
    (E F : CochainComplex
      (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)
    (hE : _root_.RingedSite.CochainComplex.IsStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) E) :
    IsIsomorphic
      (DerivedCategory.Q.obj ((ihom E).obj F))
      ((ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj F)) := sorry

end Derived

section KFlat

variable [MonoidalClosed
  (CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)]

/-- K-flat companion to Lemma 21.44.9 (08JH), used by Lemma 20.46.10: internal Hom into a K-flat
target is K-flat when the source is strictly perfect. -/
@[stacks 08JH "K-flat companion",
  stacks 0GM5 "K-flatness of internal Hom from a strictly perfect complex"]
theorem isKFlat_of_strictlyPerfect
    (E F : CochainComplex
      (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)
    (hE : _root_.RingedSite.CochainComplex.IsStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) E) (hF : F.IsKFlat) :
    ((ihom E).obj F).IsKFlat := sorry

end KFlat

section Derived

variable [MonoidalClosed
  (CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)]
variable [RingedSite.Hom.ModuleDerived.KFlat.HomotopyTensorDescends O]
variable [RingedSite.Hom.ModuleDerived.KFlat.TensorDescends O]
variable [RingedSite.Hom.ModuleDerived.KFlat.IsLocalization O]

-- Fix the tensor before asking for its closed right-adjoint data. These are the exact
-- K-flat localization hypotheses, not an arbitrary monoidal structure on the derived category.
attribute [local instance] RingedSite.Hom.ModuleDerived.monoidalCategory
variable [MonoidalClosed
  (DerivedCategory (ringedSiteModuleCategory.{u, v, w, w} J O))]

/-- Lemma 21.44.10 (08JI), equivalently Lemma 20.46.11 (08I5): an upper-bounded
finite-free-retract source and a lower-bounded target compute derived internal Hom by the
canonical internal-Hom complex. -/
@[stacks 08JI "bounded source computes derived internal Hom",
  stacks 08I5 "bounded source computes derived internal Hom"]
theorem represents_of_bounds
    (E F : CochainComplex
      (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)
    (hF : ∃ a : ℤ, F.IsStrictlyGE a)
    (hE : ∃ b : ℤ, E.IsStrictlyLE b)
    (hterms : ∀ i : ℤ,
      SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O) (E.X i)) :
    IsIsomorphic
      (DerivedCategory.Q.obj ((ihom E).obj F))
      ((ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj F)) := sorry

/-- The explicit-bound form of `represents_of_bounds`, for callers already carrying chosen
lower and upper bounds. -/
@[stacks 08JI "explicit bounds", stacks 08I5 "explicit bounds"]
theorem represents_of_strictBounds
    (E F : CochainComplex
      (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)
    {a b : ℤ} (hF : F.IsStrictlyGE a) (hE : E.IsStrictlyLE b)
    (hterms : ∀ i : ℤ,
      SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O) (E.X i)) :
    IsIsomorphic
      (DerivedCategory.Q.obj ((ihom E).obj F))
      ((ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj F)) := by
  exact represents_of_bounds E F ⟨a, hF⟩ ⟨b, hE⟩ hterms

end Derived

end RingedSite.CochainComplex.InternalHom

namespace RingedSite.CochainComplex.InternalHom.Canonical

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

-- The sheaf Hom owner constructs local morphism sheaves in this universe. Keep the more
-- general universe-polymorphic interface above until that owner also supports `UnivLE`.
local instance moduleClosed : MonoidalClosed (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) :=
  SheafOfModules.RingedSite.InternalHom.moduleMonoidalClosed O

-- This is the explicit product Hom with its signed differential and proved adjunction.
-- It is local so no alternative closed structure is installed for downstream clients.
local instance complexClosed :
    MonoidalClosed (CochainComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) ℤ) :=
  CategoryTheory.CochainComplex.InternalHom.monoidalClosed

/-- The K-flat companion for the explicit product Hom complex. It uses no derived tensor. -/
@[stacks 0GM5 "canonical complex K-flat companion"]
theorem isKFlat_of_strictlyPerfect
    (E F : CochainComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) ℤ)
    (hE : _root_.RingedSite.CochainComplex.IsStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) E) (hF : F.IsKFlat) :
    (CategoryTheory.CochainComplex.InternalHom.obj E F).IsKFlat :=
  _root_.RingedSite.CochainComplex.InternalHom.isKFlat_of_strictlyPerfect E F hE hF

variable [RingedSite.Hom.ModuleDerived.KFlat.HomotopyTensorDescends (C := C) (J := J) O]
variable [RingedSite.Hom.ModuleDerived.KFlat.TensorDescends (C := C) (J := J) O]
variable [RingedSite.Hom.ModuleDerived.KFlat.IsLocalization (C := C) (J := J) O]
attribute [local instance] RingedSite.Hom.ModuleDerived.monoidalCategory
variable [MonoidalClosed (DerivedCategory (ringedSiteModuleCategory.{u, v, max u v, max u v} J O))]

/-- The source specialization with the actual product Hom complex. The derived closed data
belongs to the exact K-flat localization tensor, as in the reusable structural interface. -/
@[stacks 08JH "canonical strictly perfect Hom complex",
  stacks 08DM "canonical strictly perfect Hom complex"]
theorem represents_of_strictlyPerfect
    (E F : CochainComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) ℤ)
    (hE : _root_.RingedSite.CochainComplex.IsStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) E) :
    IsIsomorphic
      (DerivedCategory.Q.obj (CategoryTheory.CochainComplex.InternalHom.obj E F))
      ((ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj F)) :=
  _root_.RingedSite.CochainComplex.InternalHom.represents_of_strictlyPerfect E F hE

/-- Upper/lower bounded source specialization using the actual product Hom complex. The
bounds make each relevant diagonal finite; finite-free retracts give termwise exactness of Hom. -/
@[stacks 08JI "canonical bounded Hom complex", stacks 08I5 "canonical bounded Hom complex"]
theorem represents_of_bounds
    (E F : CochainComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) ℤ)
    (hF : ∃ a : ℤ, F.IsStrictlyGE a)
    (hE : ∃ b : ℤ, E.IsStrictlyLE b)
    (hterms : ∀ i : ℤ,
      SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O) (E.X i)) :
    IsIsomorphic
      (DerivedCategory.Q.obj (CategoryTheory.CochainComplex.InternalHom.obj E F))
      ((ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj F)) :=
  _root_.RingedSite.CochainComplex.InternalHom.represents_of_bounds E F hF hE hterms

/-- The explicit-bound specialization for the canonical product Hom complex. -/
@[stacks 08JI "canonical Hom complex with explicit bounds",
  stacks 08I5 "canonical Hom complex with explicit bounds"]
theorem represents_of_strictBounds
    (E F : CochainComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) ℤ)
    {a b : ℤ} (hF : F.IsStrictlyGE a) (hE : E.IsStrictlyLE b)
    (hterms : ∀ i : ℤ,
      SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J O) (E.X i)) :
    IsIsomorphic
      (DerivedCategory.Q.obj (CategoryTheory.CochainComplex.InternalHom.obj E F))
      ((ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj F)) :=
  represents_of_bounds E F ⟨a, hF⟩ ⟨b, hE⟩ hterms

end RingedSite.CochainComplex.InternalHom.Canonical

end
