/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/- Bounded chart/gluing construction for small étale base change.
   Public migration proposal; native validation remains a MAIN gate. -/
module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback.AdaptedCharts
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback.AdaptedGluing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.FinallySmall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale.PullbackBounds

namespace CommaFinallySmall

/-- The exact costructured-arrow category used by the pointwise Kan formula. -/
abbrev Comma (S T : Scheme.{u}) (f : T ⟶ S) (V : T.Etale) :=
  CostructuredArrow (Scheme.smallEtalePullback f).op (Opposite.op V)

/-- The adapter from the native pointwise chart family to the gluing family
used by `boundedCommaObject`.  Every scheme, open, code, and comparison map is
copied from the supplied adapted chart; no witness is selected here. -/
def asGluingFamily {S T U : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    {g : U ⟶ S} [Etale g] (C : EtaleCommaInput f V g)
    (Q : AdaptedChartFamily (canonicalBaseAtlas S) C) :
    AdaptedGluing.Family (canonicalBaseAtlas S) C where
  W := fun x => (Q x).chartOpen
  affine := fun x => (Q x).chartAffine
  baseIndex := fun x => g.base ((commaInputProjection C).base x)
  code := fun x => (Q x).code
  theta := fun x => (Q x).modelIso
  overS := fun x => (Q x).model_overS
  containsProjection := fun x => (Q x).containsProjection

/-- The default chart family is fed through the actual gluing adapter and then
through the actual bounded-comma constructor. -/
def defaultBoundedCommaObject {S T U : Scheme.{u}} {f : T ⟶ S}
    {V : T.Etale} {g : U ⟶ S} [Etale g]
    (C : EtaleCommaInput f V g) :
    BoundedCommaFamily (A := canonicalBaseAtlas S) (f := f) V :=
  AdaptedGluing.boundedCommaObject
    (asGluingFamily C (defaultAdaptedChartFamily (canonicalBaseAtlas S) C))

/-- Turn a bounded-comma member into the corresponding actual object of the
costructured arrow.  The map `k` is retained as the opposite arrow, so the
orientation is exactly `pullback(g,f)ᵒᵖ ⟶ Vᵒᵖ`. -/
noncomputable def boundedCommaObjectInComma {S T : Scheme.{u}} {f : T ⟶ S}
    {V : T.Etale}
    (k : BoundedCommaFamily (A := canonicalBaseAtlas S) (f := f) V) :
    Comma S T f V := by
  let D := k.1
  let hD := coverCompat_of_chart_over_S D
  letI : Etale (gluedToS D hD) := gluedToS_etale D hD
  let X : S.Etale := Scheme.Etale.mk (gluedToS D hD)
  let a : V ⟶ (Scheme.smallEtalePullback f).obj X :=
    MorphismProperty.Over.homMk k.2.1 k.2.2
  exact CostructuredArrow.mk (Y := Opposite.op X) a.op

/-- The code-generated family image.  Its domain is the actual Type-u
`BoundedCommaFamily`, so the native `small_range` API gives the required
universe bound. -/
def familyImage {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} :
    Set (Comma S T f V) :=
  Set.range (boundedCommaObjectInComma (S := S) (T := T) (f := f) (V := V))

theorem familyImageSmallu {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale} :
    Small.{u} (familyImage (S := S) (T := T) (f := f) (V := V)) := by
  change Small.{u} (Set.range
    (boundedCommaObjectInComma (S := S) (T := T) (f := f) (V := V)))
  infer_instance

/-- The comma input induced by an arbitrary costructured-arrow object.  Its
second equation is exactly the opposite of the comma triangle; it is kept as a
Prop proof obligation rather than used to manufacture a map. -/
noncomputable def inputOfComma {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    (j : Comma S T f V) :
    @EtaleCommaInput S T f V j.left.unop.left j.left.unop.hom
      j.left.unop.prop := by
  letI : Etale j.left.unop.hom := j.left.unop.prop
  exact
    { h := j.hom.unop.left
      overT := MorphismProperty.Over.w j.hom.unop }

/-- The actual default target selected from an arbitrary comma object. -/
noncomputable def refinementMember {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    (j : Comma S T f V) :
    BoundedCommaFamily (A := canonicalBaseAtlas S) (f := f) V :=
  by
    letI : Etale j.left.unop.hom := j.left.unop.prop
    exact @defaultBoundedCommaObject S T j.left.unop.left f V
      j.left.unop.hom j.left.unop.prop (inputOfComma j)

/-- The explicit adapted gluing family associated to an arbitrary comma
object.  Its étale instance is the bundled property carried by the comma
object, made explicit so subsequent dependent types do not ask typeclass
inference to recover it. -/
noncomputable def refinementFamily {S T : Scheme.{u}} {f : T ⟶ S}
    {V : T.Etale} (j : Comma S T f V) :
    @AdaptedGluing.Family S T j.left.unop.left (canonicalBaseAtlas S)
      f V j.left.unop.hom j.left.unop.prop (inputOfComma j) := by
  letI : Etale j.left.unop.hom := j.left.unop.prop
  exact @asGluingFamily S T j.left.unop.left f V j.left.unop.hom
    j.left.unop.prop (inputOfComma j)
    (defaultAdaptedChartFamily (canonicalBaseAtlas S) (inputOfComma j))

/-- The comparison data used to refine an arbitrary comma object.  The source
is the arbitrary étale object `j.left.unop`; the target is the glued default
atlas supplied by `defaultAdaptedChartFamily`. -/
noncomputable def refinementComparison {S T : Scheme.{u}} {f : T ⟶ S}
    {V : T.Etale} (j : Comma S T f V) :
    @CorrectedCommaCompositionData S T f V j.left.unop.left j.left.unop.hom
      j.left.unop.prop (inputOfComma j)
      (AdaptedGluing.selection (refinementFamily j))
      (AdaptedGluing.unionLaw (refinementFamily j)) := by
  letI : Etale j.left.unop.hom := j.left.unop.prop
  exact AdaptedGluing.adaptedComparison (refinementFamily j)

/-- The actual arrow on S-side étale objects.  Its map is `r`, and its
compatibility with the structure maps to S is the proved comparison law. -/
noncomputable def refinementOverSMap {S T : Scheme.{u}} {f : T ⟶ S}
    {V : T.Etale} (j : Comma S T f V) :
    (boundedCommaObjectInComma (refinementMember j)).left.unop ⟶ j.left.unop := by
  let c := refinementComparison j
  exact MorphismProperty.Over.homMk (r c) (r_overS c).symm

/-- Refinement arrow in the exact opposite orientation.  The only remaining
proof field is the triangle equation; after taking opposites it is precisely
`t_rT_factor`, with the second projection equation supplied by `t_overT`. -/
noncomputable def refinementArrow {S T : Scheme.{u}} {f : T ⟶ S}
    {V : T.Etale} (j : Comma S T f V) :
    j ⟶ boundedCommaObjectInComma (refinementMember j) := by
  let c := refinementComparison j
  let e := refinementOverSMap j
  refine CostructuredArrow.homMk e.op ?_
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  change t c ≫ rT c = (inputOfComma j).h
  exact t_rT_factor c

/-- Every comma object admits an actual arrow to the code-generated family
image.  The witness is `refinementArrow`; no existence choice or IsIso choice
is used. -/
theorem familyImageWeaklyTerminal {S T : Scheme.{u}} {f : T ⟶ S}
    {V : T.Etale} :
    ∀ j : Comma S T f V,
      ∃ j' ∈ familyImage (S := S) (T := T) (f := f) (V := V),
        Nonempty (j ⟶ j') := by
  intro j
  refine ⟨boundedCommaObjectInComma (refinementMember j), ?_, ⟨refinementArrow j⟩⟩
  exact ⟨refinementMember j, rfl⟩

/-- Native final-smallness construction.  Filteredness is an explicit
geometric input and is not asserted by this leaf. -/
noncomputable def finallySmallOfFiltered
    {S T : Scheme.{u}} {f : T ⟶ S} {V : T.Etale}
    (hfiltered : IsFiltered (Comma S T f V)) :
    FinallySmall.{u} (Comma S T f V) := by
  letI := hfiltered
  letI : Small.{u} (familyImage (S := S) (T := T) (f := f) (V := V)) :=
    familyImageSmallu (S := S) (T := T) (f := f) (V := V)
  exact finallySmall_of_small_weakly_terminal_set
    (familyImage (S := S) (T := T) (f := f) (V := V))
    (familyImageWeaklyTerminal (S := S) (T := T) (f := f) (V := V))

/-- Full comma filteredness follows from the actual native finite-limit
preservation of base change; this is not an additional geometric premise. -/
theorem commaIsFiltered {S T : Scheme.{u}} (f : T ⟶ S) (V : T.Etale) :
    IsFiltered (Comma S T f V) := by
  letI : PreservesFiniteLimits (Scheme.smallEtalePullback f) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f))
  letI : RepresentablyFlat (Scheme.smallEtalePullback f) :=
    flat_of_preservesFiniteLimits _
  exact inferInstanceAs
    (IsFiltered (CostructuredArrow (Scheme.smallEtalePullback f).op (Opposite.op V)))

/-- Unconditional universe-u final-smallness for the actual full comma. -/
noncomputable def finallySmall {S T : Scheme.{u}} (f : T ⟶ S) (V : T.Etale) :
    FinallySmall.{u} (Comma S T f V) :=
  finallySmallOfFiltered (commaIsFiltered f V)

end CommaFinallySmall

end AlgebraicGeometry.Scheme.Etale.PullbackBounds
