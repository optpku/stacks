module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Horseshoe
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps in Property-Indexed Bounded-Below Horseshoes

This file exposes the two arrows of a property-indexed bounded-below horseshoe as maps of right
resolutions.  It also records their model and cochain computations and their zero composite.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Plus.TermsIn.QuasiIsoTo.Horseshoe

variable {A : Type u} [Category.{v} A] [Abelian A]
  {P : ObjectProperty A}
  {S : ShortComplex (CochainComplex A ℤ)}
  {R : QuasiIsoTo P S.X₁}

/-- The horseshoe left model morphism satisfies the comparison square over `S.f`. -/
@[reassoc]
theorem f_naturality (H : Horseshoe S R) :
    R.comparison ≫ (Plus.TermsIn.ι P).map H.f =
      S.f ≫ H.middleResolution.comparison := sorry

/-- The left arrow of a property-indexed horseshoe as a right-resolution map over `S.f`. -/
@[stacks 013T "left map of a property-indexed bounded-below horseshoe"]
def leftMap (H : Horseshoe S R) : Map S.f R H.middleResolution :=
  Map.mk H.f H.f_naturality

/-- The left resolution map retains the horseshoe left model morphism. -/
@[simp]
theorem leftMap_modelHom (H : Horseshoe S R) :
    H.leftMap.modelHom = H.f := sorry

/-- The underlying cochain map of the left resolution map is induced by the model inclusion. -/
@[simp]
theorem leftMap_hom (H : Horseshoe S R) :
    H.leftMap.hom = (Plus.TermsIn.ι P).map H.f := sorry

/-- The left resolution map commutes with the property-indexed resolution comparisons. -/
@[reassoc]
theorem leftMap_naturality (H : Horseshoe S R) :
    R.comparison ≫ H.leftMap.hom =
      S.f ≫ H.middleResolution.comparison := sorry

/-- The horseshoe right model morphism satisfies the comparison square over `S.g`. -/
@[reassoc]
theorem g_naturality (H : Horseshoe S R) :
    H.middleResolution.comparison ≫ (Plus.TermsIn.ι P).map H.g =
      S.g ≫ H.rightResolution.comparison := sorry

/-- The right arrow of a property-indexed horseshoe as a right-resolution map over `S.g`. -/
@[stacks 013T "right map of a property-indexed bounded-below horseshoe"]
def rightMap (H : Horseshoe S R) :
    Map S.g H.middleResolution H.rightResolution :=
  Map.mk H.g H.g_naturality

/-- The right resolution map retains the horseshoe right model morphism. -/
@[simp]
theorem rightMap_modelHom (H : Horseshoe S R) :
    H.rightMap.modelHom = H.g := sorry

/-- The underlying cochain map of the right resolution map is induced by the model inclusion. -/
@[simp]
theorem rightMap_hom (H : Horseshoe S R) :
    H.rightMap.hom = (Plus.TermsIn.ι P).map H.g := sorry

/-- The right resolution map commutes with the property-indexed resolution comparisons. -/
@[reassoc]
theorem rightMap_naturality (H : Horseshoe S R) :
    H.middleResolution.comparison ≫ H.rightMap.hom =
      S.g ≫ H.rightResolution.comparison := sorry

/-- The two right-resolution maps in a property-indexed horseshoe compose to zero after
reindexing along the zero relation of the source short complex. -/
@[simp]
theorem maps_comp (H : Horseshoe S R) :
    Map.reindex S.zero (Map.comp H.leftMap H.rightMap) =
      Map.zero R H.rightResolution := sorry

/-- The composite of the two horseshoe model morphisms is zero. -/
@[reassoc (attr := simp)]
theorem maps_comp_modelHom (H : Horseshoe S R) :
    H.leftMap.modelHom ≫ H.rightMap.modelHom = 0 := sorry

/-- The composite of the underlying cochain maps is zero. -/
@[reassoc (attr := simp)]
theorem maps_comp_hom (H : Horseshoe S R) :
    H.leftMap.hom ≫ H.rightMap.hom = 0 := sorry


end CochainComplex.Plus.TermsIn.QuasiIsoTo.Horseshoe
