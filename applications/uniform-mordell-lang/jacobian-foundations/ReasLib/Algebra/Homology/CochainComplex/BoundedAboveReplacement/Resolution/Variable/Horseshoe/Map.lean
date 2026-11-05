module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Horseshoe
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Map.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps in Property-Indexed Bounded-Above Horseshoes

This file exposes the two arrows of a property-indexed bounded-above horseshoe as maps of left
resolutions.  It also records their model and cochain computations and their zero composite.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Minus.TermsIn.QuasiIsoFrom.Horseshoe

variable {A : Type u} [Category.{v} A] [Abelian A]
  {P : ObjectProperty A}
  {S : ShortComplex (CochainComplex A ℤ)}
  {R : QuasiIsoFrom P S.X₃}

/-- The horseshoe left model morphism satisfies the comparison square over `S.f`. -/
@[reassoc]
theorem f_naturality (H : Horseshoe S R) :
    (Minus.TermsIn.ι P).map H.f ≫ H.middleResolution.comparison =
      H.leftResolution.comparison ≫ S.f := sorry

/-- The left arrow of a property-indexed horseshoe as a left-resolution map over `S.f`. -/
@[stacks 064C "left map of a property-indexed bounded-above horseshoe"]
def leftMap (H : Horseshoe S R) :
    Map S.f H.leftResolution H.middleResolution :=
  Map.mk H.f H.f_naturality

/-- The left resolution map retains the horseshoe left model morphism. -/
@[simp]
theorem leftMap_modelHom (H : Horseshoe S R) :
    H.leftMap.modelHom = H.f := sorry

/-- The underlying cochain map of the left resolution map is induced by the model inclusion. -/
@[simp]
theorem leftMap_hom (H : Horseshoe S R) :
    H.leftMap.hom = (Minus.TermsIn.ι P).map H.f := sorry

/-- The left resolution map commutes with the property-indexed resolution comparisons. -/
@[reassoc]
theorem leftMap_naturality (H : Horseshoe S R) :
    H.leftMap.hom ≫ H.middleResolution.comparison =
      H.leftResolution.comparison ≫ S.f := sorry

/-- The horseshoe right model morphism satisfies the comparison square over `S.g`. -/
@[reassoc]
theorem g_naturality (H : Horseshoe S R) :
    (Minus.TermsIn.ι P).map H.g ≫ R.comparison =
      H.middleResolution.comparison ≫ S.g := sorry

/-- The right arrow of a property-indexed horseshoe as a left-resolution map over `S.g`. -/
@[stacks 064C "right map of a property-indexed bounded-above horseshoe"]
def rightMap (H : Horseshoe S R) : Map S.g H.middleResolution R :=
  Map.mk H.g H.g_naturality

/-- The right resolution map retains the horseshoe right model morphism. -/
@[simp]
theorem rightMap_modelHom (H : Horseshoe S R) :
    H.rightMap.modelHom = H.g := sorry

/-- The underlying cochain map of the right resolution map is induced by the model inclusion. -/
@[simp]
theorem rightMap_hom (H : Horseshoe S R) :
    H.rightMap.hom = (Minus.TermsIn.ι P).map H.g := sorry

/-- The right resolution map commutes with the property-indexed resolution comparisons. -/
@[reassoc]
theorem rightMap_naturality (H : Horseshoe S R) :
    H.rightMap.hom ≫ R.comparison =
      H.middleResolution.comparison ≫ S.g := sorry

/-- The two left-resolution maps in a property-indexed horseshoe compose to zero after
reindexing along the zero relation of the source short complex. -/
@[simp]
theorem maps_comp (H : Horseshoe S R) :
    Map.reindex S.zero (Map.comp H.leftMap H.rightMap) =
      Map.zero H.leftResolution R := sorry

/-- The composite of the two horseshoe model morphisms is zero. -/
@[reassoc (attr := simp)]
theorem maps_comp_modelHom (H : Horseshoe S R) :
    H.leftMap.modelHom ≫ H.rightMap.modelHom = 0 := sorry

/-- The composite of the underlying cochain maps is zero. -/
@[reassoc (attr := simp)]
theorem maps_comp_hom (H : Horseshoe S R) :
    H.leftMap.hom ≫ H.rightMap.hom = 0 := sorry


end CochainComplex.Minus.TermsIn.QuasiIsoFrom.Horseshoe
