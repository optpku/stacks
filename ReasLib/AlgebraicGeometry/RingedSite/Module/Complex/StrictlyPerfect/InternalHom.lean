/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Complex
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
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
variable [MonoidalCategory
  (DerivedCategory (ringedSiteModuleCategory.{u, v, w, w} J O))]
variable [MonoidalClosed
  (DerivedCategory (ringedSiteModuleCategory.{u, v, w, w} J O))]

/- The ambient monoidal and derived-category structures are explicit interfaces.  The theorem
   does not rebuild them from proof-local instances, so downstream users can supply the canonical
   owners or another compatible model. -/

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
variable [MonoidalCategory
  (DerivedCategory (ringedSiteModuleCategory.{u, v, w, w} J O))]
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
      ((ihom (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj F)) := sorry

end Derived

end RingedSite.CochainComplex.InternalHom

end
