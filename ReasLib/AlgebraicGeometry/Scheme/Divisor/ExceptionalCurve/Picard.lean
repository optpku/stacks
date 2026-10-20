module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Contraction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

@[expose] public section

open CategoryTheory
open AddEquiv
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsExceptionalCurveFirstKind

/-- The degree on the Picard group of `X` obtained by restricting to an exceptional curve `E`
and identifying `E` with a projective line. -/
noncomputable def degreeFromProjectiveLine {X : Scheme.{u}} (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] {k : Type u} [Field k]
    (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme) : X.PicardGroup →+ ℤ where
  toFun x :=
    Scheme.Modules.curveDegreeOfInvertible (ProjectiveSpace.toSpec k 1)
      (ProjectiveSpace.topologicalKrullDim_scheme_eq k 1).le
      ((Scheme.Modules.pullback (e.hom ≫ E.subschemeι)).obj
        (Scheme.PicardGroup.repr x))
  map_zero' := sorry
  map_add' := sorry

/-- Evaluation of the exceptional-curve degree through a chosen projective-line presentation. -/
theorem degreeFromProjectiveLine_apply {X : Scheme.{u}} (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] {k : Type u} [Field k]
    (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme) (x : X.PicardGroup) :
    degreeFromProjectiveLine E e x =
      Scheme.Modules.curveDegreeOfInvertible (ProjectiveSpace.toSpec k 1)
        (ProjectiveSpace.topologicalKrullDim_scheme_eq k 1).le
        ((Scheme.Modules.pullback (e.hom ≫ E.subschemeι)).obj
          (Scheme.PicardGroup.repr x)) := sorry

/-- The degree homomorphism obtained by restricting Picard classes to an exceptional curve. -/
noncomputable def degree {X : Scheme.{u}} (E : X.IdealSheafData)
    [hE : IsExceptionalCurveFirstKind E] : X.PicardGroup →+ ℤ :=
  let k : Type u := Classical.choose hE.projectiveLineNormal
  let hField := Classical.choose_spec hE.projectiveLineNormal
  let field : Field k := Classical.choose hField
  let e := Classical.choose (Classical.choose_spec hField)
  @degreeFromProjectiveLine X E hE k field e

/-- The exceptional-curve degree is induced by one of the projective-line presentations supplied
by the exceptional-curve hypothesis. -/
theorem degree_eq_degreeFromProjectiveLine {X : Scheme.{u}} (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] :
    ∃ (k : Type u) (_ : Field k) (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme),
      degree E = degreeFromProjectiveLine E e := sorry

/-- The exceptional-curve degree, lifted to the universe of the Picard group for use in `Ab`. -/
noncomputable def degreeUlift {X : Scheme.{u}} (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] : X.PicardGroup →+ ULift.{u + 1} ℤ :=
  (ulift : ULift.{u + 1} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp (degree E)

/-- The lifted exceptional-curve degree evaluates to the lift of the ordinary integer degree. -/
theorem degreeUlift_apply {X : Scheme.{u}} (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] (x : X.PicardGroup) :
    degreeUlift E x = ULift.up (degree E x) := sorry

/-- The Picard-group map sending `n` to the class of `𝒪_X(-nE)`. -/
noncomputable def exceptionalTwist {X : Scheme.{u}} (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] : ℤ →+ X.PicardGroup where
  toFun n := (-n) • Scheme.Modules.picardClass E.associatedSheaf
  map_zero' := sorry
  map_add' := sorry

/-- The exceptional twist at `n` is the class of `𝒪_X(-nE)`. -/
theorem exceptionalTwist_apply {X : Scheme.{u}} (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] (n : ℤ) :
    exceptionalTwist E n =
      (-n) • Scheme.Modules.picardClass E.associatedSheaf := sorry

/-- Pullback along a contraction has degree zero on its exceptional curve. -/
theorem picardPullback_comp_degreeUlift_zero
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x) :
    AddCommGrpCat.ofHom (Scheme.Hom.picardPullback b) ≫
      AddCommGrpCat.ofHom (degreeUlift E) = 0 := sorry

/-- The Picard-group complex of a contraction, with pullback followed by degree on the
exceptional curve. -/
noncomputable def picardDegreeSequence
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x) :
    ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (Scheme.Hom.picardPullback b))
    (AddCommGrpCat.ofHom (degreeUlift E))
    (picardPullback_comp_degreeUlift_zero E b x hb)

/-- Pullback and degree on the exceptional curve form the short exact sequence
`0 ⟶ PicardGroup X' ⟶ PicardGroup X ⟶ ℤ ⟶ 0` for a contraction. -/
theorem picardDegreeSequence_shortExact
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x) :
    (picardDegreeSequence E b x hb).ShortExact := sorry

/-- The map `n ↦ 𝒪_X(-nE)` splits the degree map in the Picard-group sequence of a contraction. -/
theorem picardDegreeSequence_splitByExceptionalTwist
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x) :
    (degree E).comp (exceptionalTwist E) = AddMonoidHom.id ℤ := sorry

end AlgebraicGeometry.IsExceptionalCurveFirstKind
