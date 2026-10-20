module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Reindex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Graded
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.GradedPullback
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Quadruple
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Representability
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.TwistGluing

/-!
# Twist comparisons associated to fixed-degree relative projective quadruples

An associated morphism to a scheme representing relative projective spectrum pulls the
degree-`d` reindexing of the universal twist algebra back to the integral tensor-power algebra
of the quadruple's invertible module.  Compatibility records the induced pushforward diagram.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeProjDegreeQuadruple

variable {S : Scheme.{u}}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
variable {d : ℕ}

/-- A morphism to a representing scheme is associated to a fixed-degree quadruple when it lies
over the quadruple's structure morphism and pulls the represented universal point back from the
ambient functor to a degree-chart point representing that quadruple. -/
def IsAssociatedMorphism
    [F : RelativeProjFunctor S 𝒜] (hd : 1 ≤ d)
    (associatedToQuadruples :
      (F.degreeFunctor ⟨d, hd⟩).IsAssociatedToQuadruples)
    {X T : Scheme.{u}} (π : X ⟶ S)
    (representedPoint : F.toFunctor.obj (op X))
    (q : RelativeProjDegreeQuadruple 𝒜 d T) (r : T ⟶ X) : Prop :=
  r ≫ π = q.morphism ∧
    ∃ degreePoint : (F.degreeFunctor ⟨d, hd⟩).toFunctor.obj (op T),
      associatedToQuadruples.associated T degreePoint q ∧
        (F.degreeToFunctor ⟨d, hd⟩).app (op T) degreePoint =
          F.toFunctor.map (op r) representedPoint

/-- Association with a representing morphism is exactly the over-base equality together with a
degree-chart point representing the quadruple and mapping to the pulled-back universal point. -/
theorem isAssociatedMorphism_spec
    [F : RelativeProjFunctor S 𝒜] (hd : 1 ≤ d)
    (associatedToQuadruples :
      (F.degreeFunctor ⟨d, hd⟩).IsAssociatedToQuadruples)
    {X T : Scheme.{u}} (π : X ⟶ S)
    (representedPoint : F.toFunctor.obj (op X))
    (q : RelativeProjDegreeQuadruple 𝒜 d T) (r : T ⟶ X) :
    IsAssociatedMorphism hd associatedToQuadruples π representedPoint q r ↔
      r ≫ π = q.morphism ∧
        ∃ degreePoint : (F.degreeFunctor ⟨d, hd⟩).toFunctor.obj (op T),
          associatedToQuadruples.associated T degreePoint q ∧
            (F.degreeToFunctor ⟨d, hd⟩).app (op T) degreePoint =
              F.toFunctor.map (op r) representedPoint := Iff.rfl

/-- The integral tensor powers of the invertible module in a quadruple, as a graded algebra
sheaf with the invertibility witness supplied explicitly. -/
noncomputable def tensorPowerGradedAlgebra
    {T : Scheme.{u}} (q : RelativeProjDegreeQuadruple 𝒜 d T) :
    GradedAlgebraSheaf.{u, u} T.sheaf ℤ :=
  @RingedSpace.InvertiblePower.gradedAlgebra _ q.lineBundle
    (Scheme.Modules.Invertible.ringedSpaceIsInvertible q.lineBundle_invertible)

/-- The degree-`n` part of the tensor-power graded algebra is the `n`th integral tensor power. -/
@[simp]
theorem tensorPowerGradedAlgebra_apply
    {T : Scheme.{u}} (q : RelativeProjDegreeQuadruple 𝒜 d T) (n : ℤ) :
    tensorPowerGradedAlgebra q n =
      @RingedSpace.InvertiblePower.sheaf _ q.lineBundle
        (Scheme.Modules.Invertible.ringedSpaceIsInvertible q.lineBundle_invertible) n := rfl

/-- A graded-algebra comparison between the pulled-back degree-`d` universal twists and the
integral tensor powers of the invertible module in a quadruple. -/
def TwistComparison
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {model : ∀ (U : S.affineOpens) (n : ℕ),
      (𝒜 (Int.ofNat n)).val.obj (op (U : S.Opens)) ≃ sectionGrading U n}
    {X T : Scheme.{u}} {π : X ⟶ S}
    (presentation : Scheme.RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model π)
    (r : T ⟶ X) (q : RelativeProjDegreeQuadruple 𝒜 d T) : Type u :=
  Scheme.RelativeProjGradedPullback r
    (GradedAlgebraSheaf.veronese (𝒪 := X.sheaf) presentation.twistAlgebra d)
    (tensorPowerGradedAlgebra q)

/-- The source degree of a twist comparison is the pullback of the universal twist in degree
`n * d`. -/
@[simp]
theorem twistComparison_source_apply
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {model : ∀ (U : S.affineOpens) (n : ℕ),
      (𝒜 (Int.ofNat n)).val.obj (op (U : S.Opens)) ≃ sectionGrading U n}
    {X : Scheme.{u}} {π : X ⟶ S}
    (presentation : Scheme.RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model π) (n : ℤ) :
    GradedAlgebraSheaf.veronese (𝒪 := X.sheaf) presentation.twistAlgebra d n =
      presentation.twistAlgebra (n * Int.ofNat d) := rfl

/-- The degree-`n` pushforward map induced by a twist comparison and an equality of structure
morphisms. -/
noncomputable def twistComparisonPushforwardHom
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {model : ∀ (U : S.affineOpens) (n : ℕ),
      (𝒜 (Int.ofNat n)).val.obj (op (U : S.Opens)) ≃ sectionGrading U n}
    {X T : Scheme.{u}} {π : X ⟶ S}
    (presentation : Scheme.RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model π)
    (r : T ⟶ X) (q : RelativeProjDegreeQuadruple 𝒜 d T)
    (θ : TwistComparison presentation r q) (h_over : r ≫ π = q.morphism)
    (n : ℕ) :
    (Scheme.Modules.pushforward π).obj
        (presentation.twistAlgebra (Int.ofNat (n * d))) ⟶
      (Scheme.Modules.pushforward q.morphism).obj
        (RingedSpace.TensorPower.sheaf q.lineBundle n) :=
  let M := presentation.twistAlgebra ((n : ℤ) * Int.ofNat d)
  let integralPower := tensorPowerGradedAlgebra q (n : ℤ)
  let adjointHom : M ⟶ (Scheme.Modules.pushforward r).obj integralPower :=
    ((Scheme.Modules.pullbackPushforwardAdjunction r).homEquiv M integralPower)
      ((θ.degreeIso (n : ℤ)).hom)
  (Scheme.Modules.pushforward π).map
      (eqToHom (congrArg presentation.twistAlgebra (Int.natCast_mul n d))) ≫
    (Scheme.Modules.pushforward π).map adjointHom ≫
    (Scheme.Modules.pushforwardComp r π).hom.app integralPower ≫
    (Scheme.Modules.pushforwardCongr h_over).hom.app integralPower ≫
    (Scheme.Modules.pushforward q.morphism).map
      ((@RingedSpace.InvertiblePower.natIso _ q.lineBundle
        (Scheme.Modules.Invertible.ringedSpaceIsInvertible q.lineBundle_invertible) n).inv)

/-- A twist comparison is compatible with the quadruple when it lies over the same base
morphism and the induced pushforward map agrees degreewise with the quadruple's map. -/
def IsCompatibleTwistComparison
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {model : ∀ (U : S.affineOpens) (n : ℕ),
      (𝒜 (Int.ofNat n)).val.obj (op (U : S.Opens)) ≃ sectionGrading U n}
    {X T : Scheme.{u}} {π : X ⟶ S}
    (presentation : Scheme.RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model π)
    (r : T ⟶ X) (q : RelativeProjDegreeQuadruple 𝒜 d T)
    (θ : TwistComparison presentation r q) : Prop :=
  ∃ h_over : r ≫ π = q.morphism,
    ∀ n : ℕ,
      presentation.psi.hom (n * d) ≫
          twistComparisonPushforwardHom presentation r q θ h_over n =
        q.psi n

/-- Compatibility exposes both the over-base equality and every degree of the commutative
pushforward diagram. -/
theorem twistComparison_spec
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {model : ∀ (U : S.affineOpens) (n : ℕ),
      (𝒜 (Int.ofNat n)).val.obj (op (U : S.Opens)) ≃ sectionGrading U n}
    {X T : Scheme.{u}} {π : X ⟶ S}
    (presentation : Scheme.RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model π)
    (r : T ⟶ X) (q : RelativeProjDegreeQuadruple 𝒜 d T)
    (θ : TwistComparison presentation r q) :
    IsCompatibleTwistComparison presentation r q θ ↔
      ∃ h_over : r ≫ π = q.morphism,
        ∀ n : ℕ,
          presentation.psi.hom (n * d) ≫
              twistComparisonPushforwardHom presentation r q θ h_over n =
            q.psi n := Iff.rfl

/-- An associated morphism to a representing relative projective scheme determines a unique
graded-algebra comparison between the pulled-back degree-`d` twists and the integral powers of
the quadruple's invertible module. -/
theorem existsUnique_twistComparison_of_isAssociatedMorphism
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
    (d : ℕ) (hd : 1 ≤ d) [F : RelativeProjFunctor S 𝒜]
    (associatedToQuadruples :
      (F.degreeFunctor ⟨d, hd⟩).IsAssociatedToQuadruples)
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (model : ∀ (U : S.affineOpens) (n : ℕ),
      (𝒜 (Int.ofNat n)).val.obj (op (U : S.Opens)) ≃ sectionGrading U n)
    {X : Scheme.{u}} (π : X ⟶ S)
    (representedPoint : F.toFunctor.obj (op X))
    (representedPoint_isUniversal : F.toFunctor.IsRepresentedBy representedPoint)
    (presentation : Scheme.RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model π)
    {T : Scheme.{u}} (q : RelativeProjDegreeQuadruple 𝒜 d T) (r : T ⟶ X)
    (h_assoc : IsAssociatedMorphism hd associatedToQuadruples π representedPoint q r) :
    ∃! θ : TwistComparison presentation r q,
      IsCompatibleTwistComparison presentation r q θ := sorry

end AlgebraicGeometry.RelativeProjDegreeQuadruple
