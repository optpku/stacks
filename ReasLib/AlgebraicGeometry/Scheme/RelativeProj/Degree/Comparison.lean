module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.GradedPullback

/-!
# Comparison data for relative projective-spectrum functors

This leaf packages a chosen graded pullback together with the pointwise data
needed to compare the associated degreewise relative projective-spectrum
functors.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
variable {d : ℕ}

/-- A degreewise relative projective-spectrum functor attached to a concrete pulled-back graded
algebra, together with explicit pointwise base-change data. -/
structure RelativeProjDegreeFunctorPullback
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d) where
  /-- The chosen graded algebra sheaf over the target scheme. -/
  algebra : GradedAlgebraSheaf.{u, u} S'.sheaf
  /-- The degreewise relative projective-spectrum functor of the chosen algebra. -/
  toRelativeProjDegreeFunctor : RelativeProjDegreeFunctor S' algebra d
  /-- The concrete graded-algebra pullback data. -/
  comparison : RelativeProjGradedPullback g 𝒜 algebra
  /-- The pointwise equivalence between the pulled-back and original relative projective-spectrum
  data. -/
  pointEquiv : ∀ (T : Schemeᵒᵖ) (t : (yoneda.obj S').obj T),
    toRelativeProjDegreeFunctor.pointOver T t ≃ F_d.pointOver T (t ≫ g)
  /-- The raw forward point maps induced by `pointEquiv` are natural in the test scheme. -/
  pointEquiv_natural : ∀ {T T' : Schemeᵒᵖ} (a : T ⟶ T'),
    toRelativeProjDegreeFunctor.toFunctor.map a ≫
        TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
          g F_d algebra toRelativeProjDegreeFunctor pointEquiv T') =
      TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
        g F_d algebra toRelativeProjDegreeFunctor pointEquiv T) ≫
        (relativeProjDegreeBaseChangeFunctor g F_d).map a

namespace RelativeProjDegreeFunctorPullback

/-- Construct a pulled-back degreewise relative projective-spectrum functor
from its algebra, graded pullback, pointwise fiber equivalences, and naturality. -/
def ofPointEquiv
    {g : S' ⟶ S} {F_d : RelativeProjDegreeFunctor S 𝒜 d}
    (algebra : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (toRelativeProjDegreeFunctor : RelativeProjDegreeFunctor S' algebra d)
    (comparison : RelativeProjGradedPullback g 𝒜 algebra)
    (pointEquiv : ∀ (T : Schemeᵒᵖ) (t : (yoneda.obj S').obj T),
      toRelativeProjDegreeFunctor.pointOver T t ≃ F_d.pointOver T (t ≫ g))
    (pointEquiv_natural : ∀ {T T' : Schemeᵒᵖ} (a : T ⟶ T'),
      toRelativeProjDegreeFunctor.toFunctor.map a ≫
          TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
            g F_d algebra toRelativeProjDegreeFunctor pointEquiv T') =
        TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
          g F_d algebra toRelativeProjDegreeFunctor pointEquiv T) ≫
          (relativeProjDegreeBaseChangeFunctor g F_d).map a) :
    RelativeProjDegreeFunctorPullback g F_d where
  algebra := algebra
  toRelativeProjDegreeFunctor := toRelativeProjDegreeFunctor
  comparison := comparison
  pointEquiv := pointEquiv
  pointEquiv_natural := pointEquiv_natural

/-- The functor on test schemes underlying a chosen pulled-back degreewise relative
projective-spectrum functor. -/
abbrev toFunctor
    {g : S' ⟶ S} {F_d : RelativeProjDegreeFunctor S 𝒜 d}
    (F'_d : RelativeProjDegreeFunctorPullback g F_d) :
    Schemeᵒᵖ ⥤ Type u :=
  F'_d.toRelativeProjDegreeFunctor.toFunctor

/-- The graded operations and pointwise fiber equivalences of a pullback package
satisfy their transport and naturality conditions. -/
theorem conditions_spec
    {g : S' ⟶ S} {F_d : RelativeProjDegreeFunctor S 𝒜 d}
    (F'_d : RelativeProjDegreeFunctorPullback g F_d) :
    ((∀ U : (S'.Opens)ᵒᵖ,
        F'_d.comparison.degreeMap 0 U (F'_d.comparison.pullbackOne U) =
          F'_d.algebra.one U) ∧
      (∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ)
        (a : pulledBackGradedAlgebraSection g 𝒜 n U)
        (b : pulledBackGradedAlgebraSection g 𝒜 m U),
        F'_d.comparison.degreeMap (n + m) U
            (F'_d.comparison.pullbackMul U n m a b) =
          F'_d.algebra.mul U n m (F'_d.comparison.degreeMap n U a)
            (F'_d.comparison.degreeMap m U b))) ∧
      ∀ {T T' : Schemeᵒᵖ} (a : T ⟶ T'),
        F'_d.toRelativeProjDegreeFunctor.toFunctor.map a ≫
            TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
              g F_d F'_d.algebra F'_d.toRelativeProjDegreeFunctor F'_d.pointEquiv T') =
          TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
            g F_d F'_d.algebra F'_d.toRelativeProjDegreeFunctor F'_d.pointEquiv T) ≫
            (relativeProjDegreeBaseChangeFunctor g F_d).map a := sorry

end RelativeProjDegreeFunctorPullback

/-- Explicit data comparing the base change of one degreewise relative projective-spectrum
functor to a second one over the target scheme. -/
structure RelativeProjDegreeFunctorBaseChangeComparison
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d) where
  /-- The graded-algebra pullback comparison. -/
  pullback : RelativeProjGradedPullback g 𝒜 𝒜'
  /-- The pointwise base-change equivalences. -/
  pointEquiv : ∀ (T : Schemeᵒᵖ) (t : (yoneda.obj S').obj T),
    F'_d.pointOver T t ≃ F_d.pointOver T (t ≫ g)
  /-- Naturality of the raw forward point maps induced by `pointEquiv`. -/
  pointEquiv_natural : ∀ {T T' : Schemeᵒᵖ} (a : T ⟶ T'),
    F'_d.toFunctor.map a ≫
        TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
          g F_d 𝒜' F'_d pointEquiv T') =
      TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
        g F_d 𝒜' F'_d pointEquiv T) ≫
        (relativeProjDegreeBaseChangeFunctor g F_d).map a

namespace RelativeProjDegreeFunctorBaseChangeComparison

/-- The graded operations and pointwise fiber equivalences of a base-change
comparison satisfy their transport and naturality conditions. -/
theorem conditions_spec
    {g : S' ⟶ S} {F_d : RelativeProjDegreeFunctor S 𝒜 d}
    {𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf}
    {F'_d : RelativeProjDegreeFunctor S' 𝒜' d}
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d) :
    ((∀ U : (S'.Opens)ᵒᵖ,
        comparison.pullback.degreeMap 0 U (comparison.pullback.pullbackOne U) =
          𝒜'.one U) ∧
      (∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ)
        (a : pulledBackGradedAlgebraSection g 𝒜 n U)
        (b : pulledBackGradedAlgebraSection g 𝒜 m U),
        comparison.pullback.degreeMap (n + m) U
            (comparison.pullback.pullbackMul U n m a b) =
          𝒜'.mul U n m (comparison.pullback.degreeMap n U a)
            (comparison.pullback.degreeMap m U b))) ∧
      ∀ {T T' : Schemeᵒᵖ} (a : T ⟶ T'),
        F'_d.toFunctor.map a ≫
            TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
              g F_d 𝒜' F'_d comparison.pointEquiv T') =
          TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
            g F_d 𝒜' F'_d comparison.pointEquiv T) ≫
            (relativeProjDegreeBaseChangeFunctor g F_d).map a := sorry

end RelativeProjDegreeFunctorBaseChangeComparison

namespace RelativeProjDegreeFunctorPullback

/-- The full comparison data carried by a chosen pullback degreewise relative
projective-spectrum functor. -/
def toBaseChangeComparison
    {g : S' ⟶ S} {F_d : RelativeProjDegreeFunctor S 𝒜 d}
    (F'_d : RelativeProjDegreeFunctorPullback g F_d) :
    RelativeProjDegreeFunctorBaseChangeComparison
      g F_d F'_d.algebra F'_d.toRelativeProjDegreeFunctor where
  pullback := F'_d.comparison
  pointEquiv := F'_d.pointEquiv
  pointEquiv_natural := F'_d.pointEquiv_natural

end RelativeProjDegreeFunctorPullback

end AlgebraicGeometry.Scheme
