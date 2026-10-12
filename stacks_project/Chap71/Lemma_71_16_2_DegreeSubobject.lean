/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_16_1_Quotient

/-!
# Quotients of relative Proj by a finite-type degree subobject

A closed subspace of `underline{Proj}_X(𝒜)` is cut out by a single
nonnegative degree subobject `G ⊂ 𝒜_d` when the corresponding quotient
presentation is universal among graded-algebra maps that kill `G`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsCommutative] [𝒜.IsQuasicoherent]
variable {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
variable {hF : F.IsAssociatedToQuadruples deg}
variable {Z : AlgebraicSpace S} {i : Z ⟶ toAlgebraicSpace F hF}
variable [IsClosedImmersion i]

namespace ClosedSubspaceQuotient

/-- A closed-subspace quotient presentation is the relative Proj of `𝒜 / G 𝒜`
when the quotient map kills the degree-`d` subobject `G` and is universal
among graded-algebra maps that kill `G`. -/
def IsQuotientByDegreeSubobject (Q : ClosedSubspaceQuotient F hF i)
    (d : ℕ) (G : Subobject (deg.obj d)) : Prop :=
  Modules.liftModuleMap G.arrow ≫ (deg.iso d).hom ≫
      Q.quotientMap.hom (Int.ofNat d) = 0 ∧
    ∀ (ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
      (g : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ),
      (Modules.liftModuleMap G.arrow ≫ (deg.iso d).hom ≫
          g.hom (Int.ofNat d) = 0) ↔
        ∃! φ : GradedAlgebraSheaf.Hom.{u + 1, u} Q.algebra ℬ,
          GradedAlgebraSheaf.Hom.comp Q.quotientMap φ = g

/-- Being a degree-subobject quotient means the quotient map kills the generating
subobject and is universal among graded-algebra maps that kill it. -/
theorem isQuotientByDegreeSubobject_iff
    (Q : ClosedSubspaceQuotient F hF i) (d : ℕ) (G : Subobject (deg.obj d)) :
    Q.IsQuotientByDegreeSubobject d G ↔
      (Modules.liftModuleMap G.arrow ≫ (deg.iso d).hom ≫
          Q.quotientMap.hom (Int.ofNat d) = 0) ∧
        ∀ (ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
          (g : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ),
          (Modules.liftModuleMap G.arrow ≫ (deg.iso d).hom ≫
              g.hom (Int.ofNat d) = 0) ↔
            ∃! φ : GradedAlgebraSheaf.Hom.{u + 1, u} Q.algebra ℬ,
              GradedAlgebraSheaf.Hom.comp Q.quotientMap φ = g :=
  sorry

/-- A degree-subobject quotient map kills the generating subobject in degree `d`. -/
theorem isQuotientByDegreeSubobject_map_eq_zero
    (Q : ClosedSubspaceQuotient F hF i) (d : ℕ) (G : Subobject (deg.obj d))
    (h : Q.IsQuotientByDegreeSubobject d G) :
    Modules.liftModuleMap G.arrow ≫ (deg.iso d).hom ≫
      Q.quotientMap.hom (Int.ofNat d) = 0 :=
  sorry

/-- A degree-subobject quotient is universal among graded-algebra maps that kill
the generating subobject. -/
theorem isQuotientByDegreeSubobject_factor
    (Q : ClosedSubspaceQuotient F hF i) (d : ℕ) (G : Subobject (deg.obj d))
    (h : Q.IsQuotientByDegreeSubobject d G)
    (ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    (g : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ) :
    (Modules.liftModuleMap G.arrow ≫ (deg.iso d).hom ≫
        g.hom (Int.ofNat d) = 0) ↔
      ∃! φ : GradedAlgebraSheaf.Hom.{u + 1, u} Q.algebra ℬ,
        GradedAlgebraSheaf.Hom.comp Q.quotientMap φ = g :=
  sorry

/-- A degree-subobject quotient map kills the generating subobject after
transport to unlifted degree pieces. -/
theorem isQuotientByDegreeSubobject_unlifted
    (Q : ClosedSubspaceQuotient F hF i) (d : ℕ) (G : Subobject (deg.obj d))
    (h : Q.IsQuotientByDegreeSubobject d G) :
    G.arrow ≫ unliftedQuotientMap F hF i Q d = 0 :=
  sorry

end ClosedSubspaceQuotient

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
