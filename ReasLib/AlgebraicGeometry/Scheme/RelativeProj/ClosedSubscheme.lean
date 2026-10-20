module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FiniteTypeGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.TwistGluing

/-!
# Closed subschemes of relative projective spectra

This file records the canonical graded map obtained by restricting the twists of a relative
projective spectrum to a closed subscheme, together with its degreewise kernel.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation

variable {S X Z : Scheme.{u}} {p : X ⟶ S}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
variable {A σ : S.affineOpens → Type u}
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
variable [∀ U, GradedRing (sectionGrading U)]
variable {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
variable {model : ∀ (U : S.affineOpens) (d : ℕ),
  (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d}

/-- The integral twist of a relative projective spectrum restricted to a subscheme. -/
noncomputable def closedSubschemeTwist
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) (d : ℤ) : Z.Modules :=
  (Scheme.Modules.pullback i).obj (presentation.twistAlgebra d)

/-- The pushforward to the base of a nonnegative twist restricted to a subscheme. -/
noncomputable def closedSubschemeDegreePiece
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) (d : ℕ) : S.Modules :=
  (Scheme.Modules.pushforward (i ≫ p)).obj
    (presentation.closedSubschemeTwist i (Int.ofNat d))

/-- The canonical degree map from a relative-projective graded algebra to the pushforward of
the corresponding twist restricted to a closed subscheme. -/
noncomputable def closedSubschemeDegreeMap
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) :
    𝒜 (Int.ofNat d) ⟶ presentation.closedSubschemeDegreePiece i d :=
  presentation.psi.hom d ≫
    (Scheme.Modules.pushforward p).map
      (Scheme.Modules.ClosedImmersion.restrictionMap i
        (presentation.twistAlgebra (Int.ofNat d))) ≫
    (Scheme.Modules.pushforwardComp i p).hom.app
      ((Scheme.Modules.pullback i).obj (presentation.twistAlgebra (Int.ofNat d)))

/-- The degreewise kernel of the canonical map to the pushed-forward restricted twist. -/
noncomputable def closedSubschemeDegreeKernel
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) : Subobject (𝒜 (Int.ofNat d)) :=
  kernelSubobject (presentation.closedSubschemeDegreeMap i d)

/-- A presentation of a closed subscheme as the relative projective spectrum of a quotient
graded algebra, including its affine models and the canonical quotient map. -/
structure ClosedSubschemeQuotient
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i] where
  /-- The quotient graded algebra on the base. -/
  algebra : GradedAlgebraSheaf.{u, u} S.sheaf
  /-- The quotient graded algebra is commutative. -/
  algebra_isCommutative : algebra.IsCommutative
  /-- Every degree of the quotient graded algebra is quasi-coherent. -/
  algebra_isQuasicoherent : algebra.IsQuasicoherent
  /-- The affine rings used to model the quotient relative projective spectrum. -/
  affineRing : S.affineOpens → Type u
  /-- The families of homogeneous pieces in the affine models. -/
  affineGrade : S.affineOpens → Type u
  /-- Each affine model carries a commutative-ring structure. -/
  [affineRingCommRing : ∀ U, CommRing (affineRing U)]
  /-- The homogeneous pieces are represented as subsets of the affine rings. -/
  [affineGradeSetLike : ∀ U, SetLike (affineGrade U) (affineRing U)]
  /-- The homogeneous pieces are additive subgroups of the affine rings. -/
  [affineGradeAddSubgroupClass :
    ∀ U, AddSubgroupClass (affineGrade U) (affineRing U)]
  /-- The nonnegative grading on each affine model. -/
  affineGrading : ∀ U : S.affineOpens, ℕ → affineGrade U
  /-- The affine gradings are multiplicative and decompose their rings. -/
  [affineGradedRing : ∀ U, GradedRing (affineGrading U)]
  /-- The projective-spectrum twist presentation on each affine model. -/
  affinePresentation :
    ∀ U : S.affineOpens, ProjTwistPresentation (affineGrading U)
  /-- The quotient algebra's degree pieces agree with the affine homogeneous pieces. -/
  affineModel : ∀ (U : S.affineOpens) (d : ℕ),
    (algebra (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ affineGrading U d
  /-- The rich relative-projective twist presentation of the closed subscheme. -/
  quotientPresentation : RelativeProjTwist.Presentation algebra affineRing affineGrade
    affineGrading affinePresentation affineModel (i ≫ p)
  /-- The homomorphism from the original algebra to the quotient algebra. -/
  quotientMap : 𝒜 ⟶ algebra
  /-- The quotient homomorphism is degreewise epic in nonnegative degrees. -/
  quotientMap_epi : ∀ d : ℕ, Epi (quotientMap.hom (Int.ofNat d))

namespace ClosedSubschemeQuotient

/-- Construct a closed-subscheme quotient presentation from its algebra, affine models,
relative-projective presentation, quotient map, and defining properties. -/
def ofComponents
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (algebra : GradedAlgebraSheaf.{u, u} S.sheaf)
    (algebra_isCommutative : algebra.IsCommutative)
    (algebra_isQuasicoherent : algebra.IsQuasicoherent)
    (affineRing affineGrade : S.affineOpens → Type u)
    [affineRingCommRing : ∀ U, CommRing (affineRing U)]
    [affineGradeSetLike : ∀ U, SetLike (affineGrade U) (affineRing U)]
    [affineGradeAddSubgroupClass :
      ∀ U, AddSubgroupClass (affineGrade U) (affineRing U)]
    (affineGrading : ∀ U : S.affineOpens, ℕ → affineGrade U)
    [affineGradedRing : ∀ U, GradedRing (affineGrading U)]
    (affinePresentation :
      ∀ U : S.affineOpens, ProjTwistPresentation (affineGrading U))
    (affineModel : ∀ (U : S.affineOpens) (d : ℕ),
      (algebra (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ affineGrading U d)
    (quotientPresentation : RelativeProjTwist.Presentation algebra affineRing affineGrade
      affineGrading affinePresentation affineModel (i ≫ p))
    (quotientMap : 𝒜 ⟶ algebra)
    (quotientMap_epi : ∀ d : ℕ, Epi (quotientMap.hom (Int.ofNat d))) :
    ClosedSubschemeQuotient presentation i where
  algebra := algebra
  algebra_isCommutative := algebra_isCommutative
  algebra_isQuasicoherent := algebra_isQuasicoherent
  affineRing := affineRing
  affineGrade := affineGrade
  affineRingCommRing := affineRingCommRing
  affineGradeSetLike := affineGradeSetLike
  affineGradeAddSubgroupClass := affineGradeAddSubgroupClass
  affineGrading := affineGrading
  affineGradedRing := affineGradedRing
  affinePresentation := affinePresentation
  affineModel := affineModel
  quotientPresentation := quotientPresentation
  quotientMap := quotientMap
  quotientMap_epi := quotientMap_epi

/-- The defining commutativity, quasi-coherence, and epimorphy properties of a closed-subscheme
quotient presentation. -/
theorem spec
    {presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p}
    {i : Z ⟶ X} [IsClosedImmersion i]
    (Q : ClosedSubschemeQuotient presentation i) :
    Q.algebra.IsCommutative ∧
      Q.algebra.IsQuasicoherent ∧
        ∀ d : ℕ, Epi (Q.quotientMap.hom (Int.ofNat d)) := sorry

/-- A closed-subscheme quotient is generated by a subobject in degree `d` when the quotient map
kills that subobject and is universal among graded-algebra maps that kill it. -/
def IsQuotientByDegreeSubobject
    {presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p}
    {i : Z ⟶ X} [IsClosedImmersion i]
    (Q : ClosedSubschemeQuotient presentation i) (d : ℕ)
    (F : Subobject (𝒜 (Int.ofNat d))) : Prop :=
  F.arrow ≫ Q.quotientMap.hom (Int.ofNat d) = 0 ∧
    ∀ (ℬ : GradedAlgebraSheaf.{u, u} S.sheaf) (g : 𝒜 ⟶ ℬ),
      F.arrow ≫ g.hom (Int.ofNat d) = 0 ↔
        ∃! h : Q.algebra ⟶ ℬ, Q.quotientMap ≫ h = g

end ClosedSubschemeQuotient

/-- A canonical quotient presentation whose degreewise kernels are the kernels of the maps to
the pushed-forward twists restricted to the closed subscheme. -/
structure CanonicalClosedSubschemeQuotient
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i]
    extends ClosedSubschemeQuotient presentation i where
  /-- The kernel in every nonnegative degree is the canonical restricted-twist kernel. -/
  quotientMap_kernel : ∀ d : ℕ,
    kernelSubobject (quotientMap.hom (Int.ofNat d)) =
      presentation.closedSubschemeDegreeKernel i d

namespace CanonicalClosedSubschemeQuotient

/-- Equip a quotient presentation with its degreewise canonical-kernel identification. -/
def ofQuotient
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (quotient : ClosedSubschemeQuotient presentation i)
    (quotientMap_kernel : ∀ d : ℕ,
      kernelSubobject (quotient.quotientMap.hom (Int.ofNat d)) =
        presentation.closedSubschemeDegreeKernel i d) :
    CanonicalClosedSubschemeQuotient presentation i where
  toClosedSubschemeQuotient := quotient
  quotientMap_kernel := quotientMap_kernel

/-- The defining commutativity, quasi-coherence, epimorphy, and kernel properties of a canonical
closed-subscheme quotient presentation. -/
theorem spec
    {presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p}
    {i : Z ⟶ X} [IsClosedImmersion i]
    (Q : CanonicalClosedSubschemeQuotient presentation i) :
    Q.algebra.IsCommutative ∧
      Q.algebra.IsQuasicoherent ∧
        (∀ d : ℕ, Epi (Q.quotientMap.hom (Int.ofNat d))) ∧
          ∀ d : ℕ, kernelSubobject (Q.quotientMap.hom (Int.ofNat d)) =
            presentation.closedSubschemeDegreeKernel i d := sorry

end CanonicalClosedSubschemeQuotient

/-- A closed subscheme of a quasi-compact relative projective spectrum has a relative-projective
presentation by the quotient of the source graded algebra by the kernels of the canonical maps
to its pushed-forward restricted twists. -/
theorem existsClosedSubschemeQuotientPresentation
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (A σ : S.affineOpens → Type u)
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact p] :
    Nonempty (presentation.CanonicalClosedSubschemeQuotient i) := sorry

/-- Over a quasi-compact quasi-separated base, every finitely presented closed subscheme of a
quasi-compact relative projective spectrum is cut out by a finite-type quasi-coherent subobject
in one positive degree. -/
theorem existsQuotientByFiniteTypeDegreeSubobject
    [CompactSpace S] [QuasiSeparatedSpace S]
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (A σ : S.affineOpens → Type u)
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
    (presentation : RelativeProjTwist.Presentation
      𝒜 A σ sectionGrading P model p)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact p]
    [Scheme.Hom.FinitePresentation i] :
    ∃ (d : ℕ) (F : Subobject (𝒜 (Int.ofNat d)))
      (Q : presentation.ClosedSubschemeQuotient i),
      0 < d ∧
        F ∈ Scheme.Modules.finiteTypeQuasiCoherentSubobjects (𝒜 (Int.ofNat d)) ∧
          Q.IsQuotientByDegreeSubobject d F := sorry

end AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation
