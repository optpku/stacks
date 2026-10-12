/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Map
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Map.Zero
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable.Horseshoe.Map

/-!
# Horseshoes for projective resolutions of cochain complexes

This file specializes the property-indexed bounded-above horseshoe API to projective objects.  The
reusable data and map constructions are owned by `Minus.TermsIn.QuasiIsoFrom.Horseshoe`; this leaf
retains the established projective-resolution names and the projective existence theorems.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.ProjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A projective horseshoe is the projective specialization of the property-indexed bounded-above
horseshoe extending a prescribed resolution of the right term. -/
@[stacks 064C]
abbrev Horseshoe (S : ShortComplex (CochainComplex A ℤ))
    (P : ProjectiveResolution S.X₃) :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe S P

namespace Horseshoe

variable {S : ShortComplex (CochainComplex A ℤ)}
  {P : ProjectiveResolution S.X₃}

/-- Construct a projective horseshoe from the fields of the neutral property-indexed owner. -/
def mk (sourceShortExact : S.ShortExact)
    (leftResolution : ProjectiveResolution S.X₁) (middle : ProjectiveMinus A)
    (f : leftResolution.model ⟶ middle) (g : middle ⟶ P.model)
    (zero : f ≫ g = 0)
    (comparison : (ShortComplex.mk f g zero).map (ProjectiveMinus.ι A) ⟶ S)
    (comparison_left : comparison.τ₁ = leftResolution.π)
    (comparison_right : comparison.τ₃ = P.π)
    (shortExact : ((ShortComplex.mk f g zero).map (ProjectiveMinus.ι A)).ShortExact) :
    Horseshoe S P :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.mk sourceShortExact leftResolution middle f g zero
    comparison comparison_left comparison_right shortExact

/-- The source row of a projective horseshoe is short exact. -/
theorem sourceShortExact (H : Horseshoe S P) : S.ShortExact := sorry

/-- The chosen projective resolution of the left term. -/
abbrev leftResolution (H : Horseshoe S P) : ProjectiveResolution S.X₁ :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.leftResolution H

/-- The middle bounded-above complex of projective objects. -/
abbrev middle (H : Horseshoe S P) : ProjectiveMinus A :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.middle H

/-- The left arrow of the projective resolving row. -/
abbrev f (H : Horseshoe S P) : H.leftResolution.model ⟶ H.middle :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.f H

/-- The right arrow of the projective resolving row. -/
abbrev g (H : Horseshoe S P) : H.middle ⟶ P.model :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.g H

/-- The two arrows of the projective resolving row have zero composite. -/
theorem zero (H : Horseshoe S P) : H.f ≫ H.g = 0 := sorry

/-- The comparison from the projective resolving row to the source row. -/
abbrev comparison (H : Horseshoe S P) :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.comparison H

/-- The left component of the comparison is the chosen left-resolution comparison. -/
@[simp]
theorem comparison_left (H : Horseshoe S P) :
    H.comparison.τ₁ = H.leftResolution.π := sorry

/-- The right component of the comparison is the prescribed right-resolution comparison. -/
@[simp]
theorem comparison_right (H : Horseshoe S P) : H.comparison.τ₃ = P.π := sorry

/-- The projective resolving row is short exact after forgetting its bundled models. -/
theorem shortExact (H : Horseshoe S P) :
    ((ShortComplex.mk H.f H.g H.zero).map (ProjectiveMinus.ι A)).ShortExact := sorry

/-- The short exact upper resolving row of bounded-above termwise-projective complexes. -/
abbrev row (H : Horseshoe S P) : ShortComplex (ProjectiveMinus A) :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.row H

/-- The named resolving row remains short exact after forgetting to cochain complexes. -/
theorem row_shortExact (H : Horseshoe S P) :
    (H.row.map (ProjectiveMinus.ι A)).ShortExact := sorry

/-- The left object of the resolving row is the chosen left projective model. -/
@[simp]
theorem row_X₁ (H : Horseshoe S P) : H.row.X₁ = H.leftResolution.model := sorry

/-- The middle object of the resolving row is the horseshoe middle model. -/
@[simp]
theorem row_X₂ (H : Horseshoe S P) : H.row.X₂ = H.middle := sorry

/-- The right object of the resolving row is the prescribed projective model. -/
@[simp]
theorem row_X₃ (H : Horseshoe S P) : H.row.X₃ = P.model := sorry

/-- The left arrow of the resolving row is the horseshoe left model morphism. -/
@[simp]
theorem row_f (H : Horseshoe S P) : H.row.f = H.f := sorry

/-- The right arrow of the resolving row is the horseshoe right model morphism. -/
@[simp]
theorem row_g (H : Horseshoe S P) : H.row.g = H.g := sorry

/-- The comparison from the upper resolving row to the source row, expressed through `row`. -/
abbrev rowComparison (H : Horseshoe S P) : H.row.map (ProjectiveMinus.ι A) ⟶ S :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.rowComparison H

/-- The middle component of the projective horseshoe comparison. -/
abbrev middleComparison (H : Horseshoe S P) :
    (H.middle : CochainComplex A ℤ) ⟶ S.X₂ :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.middleComparison H

/-- The left component of the row comparison is the chosen left resolution comparison. -/
@[simp]
theorem rowComparison_τ₁ (H : Horseshoe S P) :
    H.rowComparison.τ₁ = H.leftResolution.π := sorry

/-- The middle component of the row comparison is the horseshoe middle comparison. -/
@[simp]
theorem rowComparison_τ₂ (H : Horseshoe S P) :
    H.rowComparison.τ₂ = H.middleComparison := sorry

/-- The right component of the row comparison is the prescribed resolution comparison. -/
@[simp]
theorem rowComparison_τ₃ (H : Horseshoe S P) : H.rowComparison.τ₃ = P.π := sorry

/-- The left comparison in a projective horseshoe is a quasi-isomorphism. -/
theorem leftComparison_quasiIso (H : Horseshoe S P) :
    QuasiIso H.comparison.τ₁ := sorry

/-- The right comparison in a projective horseshoe is a quasi-isomorphism. -/
theorem rightComparison_quasiIso (H : Horseshoe S P) :
    QuasiIso H.comparison.τ₃ := sorry

/-- The middle comparison in a projective horseshoe is a quasi-isomorphism. -/
theorem middleComparison_quasiIso (H : Horseshoe S P) :
    QuasiIso H.middleComparison := sorry

/-- The projective resolution of the middle term supplied by a horseshoe. -/
abbrev middleResolution (H : Horseshoe S P) : ProjectiveResolution S.X₂ :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.middleResolution H

/-- The bundled model of the middle resolution is the horseshoe middle object. -/
@[simp]
theorem middleResolution_model (H : Horseshoe S P) :
    H.middleResolution.model = H.middle := sorry

/-- The underlying complex of the middle resolution is the horseshoe middle complex. -/
@[simp]
theorem middleResolution_complex (H : Horseshoe S P) :
    H.middleResolution.complex = (H.middle : CochainComplex A ℤ) := sorry

/-- The comparison map of the middle resolution is the horseshoe middle comparison. -/
@[simp]
theorem middleResolution_π (H : Horseshoe S P) :
    H.middleResolution.π = H.middleComparison := sorry

/-- The horseshoe left model morphism satisfies the comparison square over `S.f`. -/
@[reassoc]
theorem f_naturality (H : Horseshoe S P) :
    (ProjectiveMinus.ι A).map H.f ≫ H.middleResolution.π =
      H.leftResolution.π ≫ S.f := sorry

/-- The left arrow of a projective horseshoe as a map of projective resolutions over `S.f`. -/
@[stacks 064C "left map of a projective horseshoe"]
abbrev leftMap (H : Horseshoe S P) : Map S.f H.leftResolution H.middleResolution :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.leftMap H

/-- The left resolution map retains the horseshoe left model morphism. -/
@[simp]
theorem leftMap_modelHom (H : Horseshoe S P) : H.leftMap.modelHom = H.f := sorry

/-- The underlying cochain map of the left resolution map is induced by the model inclusion. -/
@[simp]
theorem leftMap_hom (H : Horseshoe S P) :
    H.leftMap.hom = (ProjectiveMinus.ι A).map H.f := sorry

/-- The left resolution map commutes with the projective-resolution comparisons. -/
@[reassoc]
theorem leftMap_naturality (H : Horseshoe S P) :
    H.leftMap.hom ≫ H.middleResolution.π = H.leftResolution.π ≫ S.f := sorry

/-- The horseshoe right model morphism satisfies the comparison square over `S.g`. -/
@[reassoc]
theorem g_naturality (H : Horseshoe S P) :
    (ProjectiveMinus.ι A).map H.g ≫ P.π = H.middleResolution.π ≫ S.g := sorry

/-- The right arrow of a projective horseshoe as a map of projective resolutions over `S.g`. -/
@[stacks 064C "right map of a projective horseshoe"]
abbrev rightMap (H : Horseshoe S P) : Map S.g H.middleResolution P :=
  Minus.TermsIn.QuasiIsoFrom.Horseshoe.rightMap H

/-- The right resolution map retains the horseshoe right model morphism. -/
@[simp]
theorem rightMap_modelHom (H : Horseshoe S P) : H.rightMap.modelHom = H.g := sorry

/-- The underlying cochain map of the right resolution map is induced by the model inclusion. -/
@[simp]
theorem rightMap_hom (H : Horseshoe S P) :
    H.rightMap.hom = (ProjectiveMinus.ι A).map H.g := sorry

/-- The right resolution map commutes with the projective-resolution comparisons. -/
@[reassoc]
theorem rightMap_naturality (H : Horseshoe S P) :
    H.rightMap.hom ≫ P.π = H.middleResolution.π ≫ S.g := sorry

/-- The two projective-resolution maps in a horseshoe compose to the zero map between its outer
resolutions, after reindexing along the zero relation of the source short complex. -/
@[simp]
theorem maps_comp (H : Horseshoe S P) :
    Map.reindex S.zero (Map.comp H.leftMap H.rightMap) =
      Map.zero H.leftResolution P := sorry

/-- A projective horseshoe exists with any prescribed right projective resolution when the source
row is short exact and its left term is bounded above. -/
@[stacks 064C]
theorem nonempty [EnoughProjectives A] (hS : S.ShortExact)
    (P : ProjectiveResolution S.X₃) (h₁ : CochainComplex.minus A S.X₁) :
    Nonempty (Horseshoe S P) := sorry

/-- A projective horseshoe can preserve a common strict upper bound on a prescribed right
resolution and the left source term. -/
@[stacks 064C]
theorem exists_strictlyLE [EnoughProjectives A] (hS : S.ShortExact)
    (P : ProjectiveResolution S.X₃) (b : ℤ)
    (hP : P.complex.IsStrictlyLE b)
    (h₁ : S.X₁.IsStrictlyLE b) :
    ∃ H : Horseshoe S P,
      (H.middle : CochainComplex A ℤ).IsStrictlyLE b ∧
        H.leftResolution.complex.IsStrictlyLE b := sorry

end Horseshoe

/-- A bounded-above short exact row admits a projective horseshoe together with its right
projective resolution. -/
@[stacks 064C]
theorem exists_horseshoe [EnoughProjectives A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₁ : CochainComplex.minus A S.X₁) (h₃ : CochainComplex.minus A S.X₃) :
    Nonempty (Σ P : ProjectiveResolution S.X₃, Horseshoe S P) := sorry

/-- A bounded-above short exact row admits an upper resolving row and a comparison whose three
comparison components are quasi-isomorphisms. -/
@[stacks 064C "row-level projective horseshoe existence"]
theorem exists_horseshoe_row [EnoughProjectives A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₁ : CochainComplex.minus A S.X₁) (h₃ : CochainComplex.minus A S.X₃) :
    ∃ (row : ShortComplex (ProjectiveMinus A))
      (comparison : row.map (ProjectiveMinus.ι A) ⟶ S),
      (row.map (ProjectiveMinus.ι A)).ShortExact ∧
        QuasiIso comparison.τ₁ ∧ QuasiIso comparison.τ₂ ∧ QuasiIso comparison.τ₃ := sorry

/-- The row-level projective horseshoe can be chosen zero above degree zero when both outer
complexes are zero above degree zero. -/
@[stacks 064C "strictly nonpositive row-level projective horseshoe"]
theorem exists_horseshoe_row_strictlyLE_zero [EnoughProjectives A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₁ : S.X₁.IsStrictlyLE 0) (h₃ : S.X₃.IsStrictlyLE 0) :
    ∃ (row : ShortComplex (ProjectiveMinus A))
      (comparison : row.map (ProjectiveMinus.ι A) ⟶ S),
      (row.map (ProjectiveMinus.ι A)).ShortExact ∧
        QuasiIso comparison.τ₁ ∧ QuasiIso comparison.τ₂ ∧ QuasiIso comparison.τ₃ ∧
        (row.X₁ : CochainComplex A ℤ).IsStrictlyLE 0 ∧
        (row.X₂ : CochainComplex A ℤ).IsStrictlyLE 0 ∧
        (row.X₃ : CochainComplex A ℤ).IsStrictlyLE 0 := sorry

end CochainComplex.ProjectiveResolution
