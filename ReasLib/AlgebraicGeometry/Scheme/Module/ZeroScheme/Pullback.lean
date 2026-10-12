/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X X' : Scheme.{u}} (f : X' ⟶ X)
variable (ℒ : X.Modules) [Modules.Invertible ℒ] (s : ℒ.sections)

/-- The zero ideal of a pulled-back section is the inverse image of the original zero ideal. -/
theorem zeroIdealSheaf_sectionsPullback :
    zeroIdealSheaf ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s) =
      (zeroIdealSheaf ℒ s).comap f := sorry

/-- The zero scheme of a pulled-back section is canonically the pullback of the original
zero scheme. -/
noncomputable def zeroSchemePullbackIso
    (h_zeroIdeal : zeroIdealSheaf ((Modules.pullback f).obj ℒ)
      (Modules.sectionsPullback f ℒ s) =
      (zeroIdealSheaf ℒ s).comap f) :
    zeroScheme ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s) ≅
      pullback f (zeroSchemeι ℒ s) :=
  eqToIso (congrArg IdealSheafData.subscheme h_zeroIdeal) ≪≫
    (zeroIdealSheaf ℒ s).comapIso f

/-- The zero-scheme pullback isomorphism followed by the first projection is the zero
immersion of the pulled-back section. -/
theorem zeroSchemePullbackIso_hom_fst
    (h_zeroIdeal : zeroIdealSheaf ((Modules.pullback f).obj ℒ)
      (Modules.sectionsPullback f ℒ s) =
      (zeroIdealSheaf ℒ s).comap f) :
    (zeroSchemePullbackIso f ℒ s h_zeroIdeal).hom ≫ pullback.fst f (zeroSchemeι ℒ s) =
      zeroSchemeι ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s) := sorry

/-- The canonical morphism from the zero scheme of a pulled-back section to the original
zero scheme. -/
noncomputable def zeroSchemePullbackMap
    (h_zeroIdeal : zeroIdealSheaf ((Modules.pullback f).obj ℒ)
      (Modules.sectionsPullback f ℒ s) =
      (zeroIdealSheaf ℒ s).comap f) :
    zeroScheme ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s) ⟶
      zeroScheme ℒ s :=
  (zeroSchemePullbackIso f ℒ s h_zeroIdeal).hom ≫ pullback.snd f (zeroSchemeι ℒ s)

/-- The canonical zero-scheme pullback map makes the base-change square commute. -/
theorem zeroSchemePullbackMap_comp
    (h_zeroIdeal : zeroIdealSheaf ((Modules.pullback f).obj ℒ)
      (Modules.sectionsPullback f ℒ s) =
      (zeroIdealSheaf ℒ s).comap f) :
    zeroSchemePullbackMap f ℒ s h_zeroIdeal ≫ zeroSchemeι ℒ s =
      zeroSchemeι ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s) ≫ f := sorry

/-- The square formed by the two zero-scheme immersions and the canonical pullback map is
cartesian. -/
theorem zeroSchemePullback_isPullback
    (h_zeroIdeal : zeroIdealSheaf ((Modules.pullback f).obj ℒ)
      (Modules.sectionsPullback f ℒ s) =
      (zeroIdealSheaf ℒ s).comap f) :
    IsPullback
      (zeroSchemeι ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s))
      (zeroSchemePullbackMap f ℒ s h_zeroIdeal) f (zeroSchemeι ℒ s) := sorry

/-- Pulling back a section of an invertible module gives a cartesian square between its
zero scheme and the original zero scheme. -/
theorem zeroSchemePullbackSquare :
    IsPullback
      (zeroSchemeι ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s))
      (zeroSchemePullbackMap f ℒ s (zeroIdealSheaf_sectionsPullback f ℒ s))
      f (zeroSchemeι ℒ s) := sorry

end AlgebraicGeometry.Scheme
