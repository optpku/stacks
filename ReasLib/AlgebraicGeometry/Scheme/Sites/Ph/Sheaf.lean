/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
public import Mathlib.CategoryTheory.Sites.Coherent.RegularSheaves

/-!
# Singleton-cover sheaf criteria for the `ph` site

This leaf records the equalizer presentation of a singleton proper-surjective
cover and the resulting sheaf criteria.  The predicates are intentionally
parameterized by an arbitrary coefficient universe, so the API can be reused
for set-valued and larger-valued presheaves alike.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Scheme
namespace Ph

variable {S : Scheme.{u}}

/-- The type of sections on `V` equalized by the two projections of `V ×_U V`.

This transparent compatibility abbreviation is exactly the subtype codomain of
`regularTopology.mapToEqualizer`. It is the target for the restriction map associated with a
singleton cover `f : V ⟶ U`; it does not assume that `f` is proper or
surjective, allowing the construction to be reused for arbitrary arrows.
-/
abbrev equalizer (F : (Over S)ᵒᵖ ⥤ Type v) {U V : Over S} (f : V ⟶ U) : Type v :=
  { s : F.obj (op V) //
      F.map (pullback.fst f f).op s = F.map (pullback.snd f f).op s }

/-- Restriction along `f` satisfies the two equalizer equations. -/
theorem equalizerMap_property
    (F : (Over S)ᵒᵖ ⥤ Type v) {U V : Over S} (f : V ⟶ U)
    (s : F.obj (op U)) :
    F.map (pullback.fst f f).op (F.map f.op s) =
      F.map (pullback.snd f f).op (F.map f.op s) := by
  simp only [← comp_apply, ← Functor.map_comp, ← op_comp, pullback.condition]

/-- The canonical restriction map into the equalizer associated with `f`. -/
noncomputable def equalizerMap
    (F : (Over S)ᵒᵖ ⥤ Type v) {U V : Over S} (f : V ⟶ U) :
    F.obj (op U) → equalizer F f :=
  regularTopology.mapToEqualizer F f (pullback.fst f f) (pullback.snd f f) pullback.condition

/-- The underlying section of `equalizerMap F f s` is the restriction of `s`
along `f`. -/
@[simp]
theorem equalizerMap_val
    (F : (Over S)ᵒᵖ ⥤ Type v) {U V : Over S} (f : V ⟶ U)
    (s : F.obj (op U)) :
    (equalizerMap F f s).val = F.map f.op s := rfl

namespace Sheaf

/-- A presheaf satisfies the singleton proper-surjective sheaf condition. -/
def IsProperSurjective (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U) [IsProper f.left] [Surjective f.left],
    Presieve.IsSheafFor F (Presieve.singleton f)

/-- A presheaf satisfies the singleton proper-surjective sheaf condition on
affine targets. -/
def IsAffineProperSurjective (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U) [IsAffine U.left] [IsProper f.left]
    [Surjective f.left],
    Presieve.IsSheafFor F (Presieve.singleton f)

/-- The singleton presieve sheaf condition is equivalent to bijectivity of the
canonical map into `equalizer F f`. -/
theorem singleton_iff_bijective
    (F : (Over S)ᵒᵖ ⥤ Type v) {U V : Over S} (f : V ⟶ U) :
    Presieve.IsSheafFor F (Presieve.singleton f) ↔
      Function.Bijective (equalizerMap F f) := sorry

end Sheaf

namespace Equalizer

/-- A presheaf satisfies the proper-surjective equalizer condition. -/
def IsProperSurjective (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U) [IsProper f.left] [Surjective f.left],
    regularTopology.SingleEqualizerCondition F f

/-- A presheaf satisfies the proper-surjective equalizer condition on affine
targets. -/
def IsAffineProperSurjective (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over S⦄ (f : V ⟶ U) [IsAffine U.left] [IsProper f.left]
    [Surjective f.left],
    regularTopology.SingleEqualizerCondition F f

/-- The proper-surjective equalizer condition is equivalent to the singleton
sheaf condition. -/
theorem iffSheaf (F : (Over S)ᵒᵖ ⥤ Type v) :
    IsProperSurjective F ↔ Sheaf.IsProperSurjective F := sorry

/-- The affine-target equalizer condition is equivalent to the affine-target
singleton sheaf condition. -/
theorem iffAffineSheaf (F : (Over S)ᵒᵖ ⥤ Type v) :
    IsAffineProperSurjective F ↔ Sheaf.IsAffineProperSurjective F := sorry

/-- Under the Zariski sheaf condition, the equalizer test reduces to affine targets. -/
theorem iffAffine
    (F : (Over S)ᵒᵖ ⥤ Type v)
    (hzar : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F) :
    IsProperSurjective F ↔ IsAffineProperSurjective F := sorry

end Equalizer

namespace Sheaf

/-- The big `ph` sheaf criterion by Zariski and equalizer conditions. -/
theorem iffZariskiAndEqualizer
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (bigPhSite S) F ↔
      Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F ∧
        Equalizer.IsProperSurjective F := sorry

/-- The big `ph` sheaf criterion by Zariski and singleton conditions. -/
theorem iffZariskiAndSingleton
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (bigPhSite S) F ↔
      Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F ∧
        IsProperSurjective F := sorry

/-- The big `ph` sheaf criterion using affine-target singleton covers. -/
theorem iffZariskiAndAffine
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (bigPhSite S) F ↔
      Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F ∧
        IsAffineProperSurjective F := sorry

end Sheaf

end Ph
end AlgebraicGeometry.Scheme
