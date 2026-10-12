/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Comparison
public import ReasLib.Topology.Sheaf.HigherDirectImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheafifying the cohomology presheaf of a higher direct image

The cohomology presheaf of a sheaf on `X`, pushed forward along `f : X ⟶ Y` and sheafified, is
canonically isomorphic to its higher direct image. This file owns that natural isomorphism before
passage to stalks; the un-sheafified presheaf is intentionally retained as a separate functor.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.HigherDirectImage.Presheaf

variable {X Y : TopCat.{u}}

/-- Pushforward of the degree-`p` cohomology presheaf, functorial in the coefficient sheaf. -/
@[stacks 0A3E "pushforward of the cohomology presheaf"]
abbrev cohomologyFunctor (f : X ⟶ Y) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ Y.Presheaf AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) p ⋙
    TopCat.Presheaf.pushforward AddCommGrpCat.{u} f

/-- Sheafification of the pushed-forward degree-`p` cohomology presheaf. -/
@[stacks 0A3E "sheafified pushforward of the cohomology presheaf"]
abbrev sheafifiedCohomologyFunctor (f : X ⟶ Y) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ Y.Sheaf AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) p ⋙
    TopCat.Presheaf.sheafifiedPushforward (C := AddCommGrpCat.{u}) f

/-- The right-derived sheaf inclusion, followed by presheaf pushforward and sheafification. -/
abbrev derivedFunctor (f : X ⟶ Y) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ Y.Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.forget AddCommGrpCat.{u} X).rightDerived p ⋙
    TopCat.Presheaf.sheafifiedPushforward (C := AddCommGrpCat.{u}) f

/-- After pushforward and sheafification, the cohomology-presheaf comparison identifies the
sheafified cohomology functor with the right-derived sheaf inclusion. -/
noncomputable def cohomologyDerivedIso (f : X ⟶ Y) (p : ℕ) :
    sheafifiedCohomologyFunctor f p ≅ derivedFunctor f p :=
  Functor.isoWhiskerRight
      (CategoryTheory.Sheaf.cohomologyPresheafIso
        (Opens.grothendieckTopology X) p).symm
      (TopCat.Presheaf.sheafifiedPushforward (C := AddCommGrpCat.{u}) f)

/-- Exact postcomposition by presheaf pushforward and sheafification commutes with right
derivation. -/
noncomputable def rightDerivedPostcompIso (f : X ⟶ Y) (p : ℕ) :
    derivedFunctor f p ≅
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.sheafifiedPushforward
          (C := AddCommGrpCat.{u}) f).rightDerived p :=
  (Functor.RightDerived.postcompIso
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
    (TopCat.Presheaf.sheafifiedPushforward
      (C := AddCommGrpCat.{u}) f) p).symm

/-- Deriving the sheafified underlying-presheaf pushforward gives the higher direct image
functor. -/
noncomputable def pushforwardDerivedIso (f : X ⟶ Y) (p : ℕ) :
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.sheafifiedPushforward
        (C := AddCommGrpCat.{u}) f).rightDerived p ≅
      TopCat.Sheaf.higherDirectImageFunctor f p :=
  CategoryTheory.NatIso.rightDerived
    (TopCat.Sheaf.pushforwardSheafificationIso (C := AddCommGrpCat.{u}) f) p

/-- The derived-presheaf model, after pushforward and sheafification, computes the higher
direct image functor. -/
noncomputable def derivedIso (f : X ⟶ Y) (p : ℕ) :
    derivedFunctor f p ≅ TopCat.Sheaf.higherDirectImageFunctor f p :=
  rightDerivedPostcompIso f p ≪≫ pushforwardDerivedIso f p

/-- The sheafification of the pushed-forward cohomology presheaf is canonically the higher direct
image. -/
@[stacks 0A3E "cohomology presheaf sheafifies to the higher direct image"]
noncomputable def iso (f : X ⟶ Y) (p : ℕ) :
    sheafifiedCohomologyFunctor f p ≅ TopCat.Sheaf.higherDirectImageFunctor f p :=
  cohomologyDerivedIso f p ≪≫ derivedIso f p

/-- The coefficient-sheaf component of the canonical sheafified-cohomology comparison. -/
@[stacks 0A3E "coefficient component of the sheafified higher-direct-image comparison"]
noncomputable abbrev objIso (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (sheafifiedCohomologyFunctor f p).obj F ≅ TopCat.Sheaf.higherDirectImage f F p :=
  (iso f p).app F

/-- The canonical sheafified-cohomology comparison is natural in the coefficient sheaf. -/
@[reassoc, stacks 0A3E "coefficient naturality of the sheafified higher-direct-image comparison"]
theorem objIso_hom_naturality (f : X ⟶ Y)
    {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (p : ℕ) :
    (sheafifiedCohomologyFunctor f p).map a ≫ (objIso f G p).hom =
    (objIso f F p).hom ≫
      TopCat.Sheaf.higherDirectImageMap f a p := sorry

end TopCat.Sheaf.HigherDirectImage.Presheaf
