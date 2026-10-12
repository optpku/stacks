/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Map
public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Map.Zero
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Horseshoe.Map

/-!
# Horseshoes for injective resolutions of cochain complexes

This file specializes the property-indexed bounded-below horseshoe to injective objects.  The
neutral owner supplies the resolving row, its comparison, the middle resolution, and its maps;
this leaf retains the injective names and the existence theorems that require enough injectives.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.InjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- An injective horseshoe is the property-indexed bounded-below horseshoe specialized to
injective objects. -/
@[stacks 013T]
abbrev Horseshoe (S : ShortComplex (CochainComplex A ℤ))
    (I : InjectiveResolution S.X₁) :=
  Plus.TermsIn.QuasiIsoTo.Horseshoe S I

namespace Horseshoe

variable {S : ShortComplex (CochainComplex A ℤ)}
  {I : InjectiveResolution S.X₁}

/-- Construct an injective horseshoe from its explicit resolving row and comparison data. -/
def mk (sourceShortExact : S.ShortExact)
    (rightResolution : InjectiveResolution S.X₃) (middle : InjectivePlus A)
    (f : I.model ⟶ middle) (g : middle ⟶ rightResolution.model)
    (zero : f ≫ g = 0)
    (comparison : S ⟶ (ShortComplex.mk f g zero).map (InjectivePlus.ι A))
    (comparison_left : comparison.τ₁ = I.ι)
    (comparison_right : comparison.τ₃ = rightResolution.ι)
    (shortExact : ((ShortComplex.mk f g zero).map (InjectivePlus.ι A)).ShortExact) :
    Horseshoe S I where
  sourceShortExact := sourceShortExact
  rightResolution := rightResolution
  middle := middle
  f := f
  g := g
  zero := zero
  comparison := comparison
  comparison_left := comparison_left
  comparison_right := comparison_right
  shortExact := shortExact

/-- The short exact resolving row of bounded-below termwise-injective complexes in a horseshoe. -/
abbrev row (H : Horseshoe S I) : ShortComplex (InjectivePlus A) :=
  Plus.TermsIn.QuasiIsoTo.Horseshoe.row H

/-- The named resolving row remains short exact after forgetting to cochain complexes. -/
theorem row_shortExact (H : Horseshoe S I) :
    (H.row.map (InjectivePlus.ι A)).ShortExact := sorry

/-- The left object of the resolving row is the prescribed injective model. -/
@[simp]
theorem row_X₁ (H : Horseshoe S I) : H.row.X₁ = I.model := sorry

/-- The middle object of the resolving row is the horseshoe middle model. -/
@[simp]
theorem row_X₂ (H : Horseshoe S I) : H.row.X₂ = H.middle := sorry

/-- The right object of the resolving row is the chosen right injective model. -/
@[simp]
theorem row_X₃ (H : Horseshoe S I) : H.row.X₃ = H.rightResolution.model := sorry

/-- The left arrow of the resolving row is the horseshoe left model morphism. -/
@[simp]
theorem row_f (H : Horseshoe S I) : H.row.f = H.f := sorry

/-- The right arrow of the resolving row is the horseshoe right model morphism. -/
@[simp]
theorem row_g (H : Horseshoe S I) : H.row.g = H.g := sorry

/-- The comparison from the source row to the resolving row, expressed through `row`. -/
abbrev rowComparison (H : Horseshoe S I) : S ⟶ H.row.map (InjectivePlus.ι A) :=
  Plus.TermsIn.QuasiIsoTo.Horseshoe.rowComparison H

/-- The middle component of the comparison carried by a horseshoe. -/
abbrev middleComparison (H : Horseshoe S I) : S.X₂ ⟶ H.middle :=
  Plus.TermsIn.QuasiIsoTo.Horseshoe.middleComparison H

/-- The left component of the row comparison is the prescribed resolution comparison. -/
@[simp]
theorem rowComparison_τ₁ (H : Horseshoe S I) : H.rowComparison.τ₁ = I.ι := sorry

/-- The middle component of the row comparison is the horseshoe middle comparison. -/
@[simp]
theorem rowComparison_τ₂ (H : Horseshoe S I) :
    H.rowComparison.τ₂ = H.middleComparison := sorry

/-- The right component of the row comparison is the chosen right resolution comparison. -/
@[simp]
theorem rowComparison_τ₃ (H : Horseshoe S I) :
    H.rowComparison.τ₃ = H.rightResolution.ι := sorry

/-- The left comparison in a horseshoe is a quasi-isomorphism. -/
theorem leftComparison_quasiIso (H : Horseshoe S I) :
    QuasiIso H.comparison.τ₁ := sorry

/-- The right comparison in a horseshoe is a quasi-isomorphism. -/
theorem rightComparison_quasiIso (H : Horseshoe S I) :
    QuasiIso H.comparison.τ₃ := sorry

/-- The middle comparison in a horseshoe is a quasi-isomorphism, by
`HomologicalComplex.HomologySequence.quasiIso_τ₂` applied to its two short exact rows. -/
theorem middleComparison_quasiIso (H : Horseshoe S I) :
    QuasiIso H.middleComparison := sorry

attribute [instance] leftComparison_quasiIso rightComparison_quasiIso
  middleComparison_quasiIso

/-- The injective resolution of the middle term canonically supplied by a horseshoe. -/
abbrev middleResolution (H : Horseshoe S I) : InjectiveResolution S.X₂ :=
  Plus.TermsIn.QuasiIsoTo.Horseshoe.middleResolution H

/-- The bundled model of the middle resolution is the horseshoe middle object. -/
@[simp]
theorem middleResolution_model (H : Horseshoe S I) :
    H.middleResolution.model = H.middle := sorry

/-- The underlying complex of the middle resolution is the horseshoe middle complex. -/
@[simp]
theorem middleResolution_complex (H : Horseshoe S I) :
    H.middleResolution.complex = (H.middle : CochainComplex A ℤ) := sorry

/-- The comparison of the middle resolution is the middle comparison of the horseshoe. -/
@[simp]
theorem middleResolution_ι (H : Horseshoe S I) :
    H.middleResolution.ι = H.middleComparison := sorry

/-- The horseshoe left model morphism satisfies the comparison square over `S.f`. -/
@[reassoc]
theorem f_naturality (H : Horseshoe S I) :
    I.ι ≫ (InjectivePlus.ι A).map H.f = S.f ≫ H.middleResolution.ι := sorry

/-- The left arrow of an injective horseshoe as a map of injective resolutions over `S.f`. -/
@[stacks 013T "left map of an injective horseshoe"]
abbrev leftMap (H : Horseshoe S I) : Map S.f I H.middleResolution :=
  Plus.TermsIn.QuasiIsoTo.Horseshoe.leftMap H

/-- The left resolution map retains the horseshoe left model morphism. -/
@[simp]
theorem leftMap_modelHom (H : Horseshoe S I) : H.leftMap.modelHom = H.f := sorry

/-- The underlying cochain map of the left resolution map is induced by the model inclusion. -/
@[simp]
theorem leftMap_hom (H : Horseshoe S I) :
    H.leftMap.hom = (InjectivePlus.ι A).map H.f := sorry

/-- The left resolution map commutes with the injective-resolution comparisons. -/
@[reassoc]
theorem leftMap_naturality (H : Horseshoe S I) :
    I.ι ≫ H.leftMap.hom = S.f ≫ H.middleResolution.ι := sorry

/-- The horseshoe right model morphism satisfies the comparison square over `S.g`. -/
@[reassoc]
theorem g_naturality (H : Horseshoe S I) :
    H.middleResolution.ι ≫ (InjectivePlus.ι A).map H.g =
      S.g ≫ H.rightResolution.ι := sorry

/-- The right arrow of an injective horseshoe as a map of injective resolutions over `S.g`. -/
@[stacks 013T "right map of an injective horseshoe"]
abbrev rightMap (H : Horseshoe S I) : Map S.g H.middleResolution H.rightResolution :=
  Plus.TermsIn.QuasiIsoTo.Horseshoe.rightMap H

/-- The right resolution map retains the horseshoe right model morphism. -/
@[simp]
theorem rightMap_modelHom (H : Horseshoe S I) : H.rightMap.modelHom = H.g := sorry

/-- The underlying cochain map of the right resolution map is induced by the model inclusion. -/
@[simp]
theorem rightMap_hom (H : Horseshoe S I) :
    H.rightMap.hom = (InjectivePlus.ι A).map H.g := sorry

/-- The right resolution map commutes with the injective-resolution comparisons. -/
@[reassoc]
theorem rightMap_naturality (H : Horseshoe S I) :
    H.middleResolution.ι ≫ H.rightMap.hom = S.g ≫ H.rightResolution.ι := sorry

/-- The two injective-resolution maps in a horseshoe compose to the zero map between its outer
resolutions, after reindexing along the zero relation of the source short complex. -/
@[simp]
theorem maps_comp (H : Horseshoe S I) :
    Map.reindex S.zero (Map.comp H.leftMap H.rightMap) =
      Map.zero I H.rightResolution := sorry

/-- A horseshoe exists with any prescribed left injective resolution when the source row is
short exact and its right term is bounded below. -/
@[stacks 013T]
theorem nonempty [EnoughInjectives A] (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (h₃ : CochainComplex.plus A S.X₃) :
    Nonempty (Horseshoe S I) := sorry

/-- A horseshoe can preserve a common strict lower bound on a prescribed left resolution and
the right source term. -/
@[stacks 013T]
theorem exists_strictlyGE [EnoughInjectives A] (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (a : ℤ)
    (hI : I.complex.IsStrictlyGE a)
    (h₃ : S.X₃.IsStrictlyGE a) :
    ∃ H : Horseshoe S I,
      (H.middle : CochainComplex A ℤ).IsStrictlyGE a ∧
        H.rightResolution.complex.IsStrictlyGE a := sorry


end Horseshoe

/-- A short exact row whose outer terms are bounded below admits a horseshoe together with its
left injective resolution. -/
@[stacks 013T]
theorem exists_horseshoe [EnoughInjectives A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₁ : CochainComplex.plus A S.X₁) (h₃ : CochainComplex.plus A S.X₃) :
    Nonempty (Σ I : InjectiveResolution S.X₁, Horseshoe S I) := sorry

/-- A bounded-below short exact row admits a resolving row and a comparison with all three
comparison components quasi-isomorphisms.  This is the row-level view of `exists_horseshoe` and
is the preferred interface when an application does not need to retain the chosen resolutions
as a dependent pair. -/
@[stacks 013T "row-level horseshoe existence"]
theorem exists_horseshoe_row [EnoughInjectives A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₁ : CochainComplex.plus A S.X₁) (h₃ : CochainComplex.plus A S.X₃) :
    ∃ (row : ShortComplex (InjectivePlus A))
      (comparison : S ⟶ row.map (InjectivePlus.ι A)),
      (row.map (InjectivePlus.ι A)).ShortExact ∧
        QuasiIso comparison.τ₁ ∧ QuasiIso comparison.τ₂ ∧ QuasiIso comparison.τ₃ := sorry

/-- The row-level horseshoe can be chosen zero below degree zero when both outer complexes are
zero below degree zero. -/
@[stacks 013T "strictly nonnegative row-level horseshoe"]
theorem exists_horseshoe_row_strictlyGE_zero [EnoughInjectives A]
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₁ : S.X₁.IsStrictlyGE 0) (h₃ : S.X₃.IsStrictlyGE 0) :
    ∃ (row : ShortComplex (InjectivePlus A))
      (comparison : S ⟶ row.map (InjectivePlus.ι A)),
      (row.map (InjectivePlus.ι A)).ShortExact ∧
        QuasiIso comparison.τ₁ ∧ QuasiIso comparison.τ₂ ∧ QuasiIso comparison.τ₃ ∧
        (row.X₁ : CochainComplex A ℤ).IsStrictlyGE 0 ∧
        (row.X₂ : CochainComplex A ℤ).IsStrictlyGE 0 ∧
        (row.X₃ : CochainComplex A ℤ).IsStrictlyGE 0 := sorry


end CochainComplex.InjectiveResolution
