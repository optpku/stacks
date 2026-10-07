module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.FinitePresentation
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Filtered colimits of finitely presented algebras on QCQS algebraic spaces

If `X` is a quasi-compact quasi-separated algebraic space over a scheme `S`,
every quasi-coherent `𝒪_X`-algebra is a small filtered colimit of finitely
presented quasi-coherent `𝒪_X`-algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- A quasi-coherent `𝒪_X`-algebra is finitely presented if, for every affine object of
`X_étale`, the algebra of sections is of finite presentation over the corresponding
structure-sheaf sections. -/
class IsFinitePresentation {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) : Prop where
  /-- Section algebras on affine étale objects are of finite presentation. -/
  finitePresentation_affineEtale :
    ∀ U : affineEtaleSite X,
      Algebra.FinitePresentation Γ(U.obj.left.left, ⊤) (sectionRing A U.obj)

/-- Finite presentation of a quasi-coherent `𝒪_X`-algebra is equivalent to finite presentation
of its section algebras on every affine étale object. -/
theorem isFinitePresentation_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    IsFinitePresentation A ↔
      ∀ U : affineEtaleSite X,
        Algebra.FinitePresentation Γ(U.obj.left.left, ⊤) (sectionRing A U.obj) :=
  sorry

/-- The structure sheaf `𝒪_X` is finitely presented as an `𝒪_X`-algebra. -/
instance instIsFinitePresentation_structureQcAlgebra {S : Scheme.{u}}
    (X : AlgebraicSpace S) : IsFinitePresentation (structureQcAlgebra X) :=
  sorry

/-- The property of an `𝒪_X`-algebra of being quasi-coherent and finitely presented. -/
def finitelyPresentableProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (Under (commRingStructureSheaf X)) :=
  fun B ↦ ∃ h : qcAlgebraUnderProperty X B, IsFinitePresentation ⟨B, h⟩

/-- Membership in `finitelyPresentableProperty X` means the algebra is quasi-coherent and
finitely presented. -/
theorem finitelyPresentableProperty_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commRingStructureSheaf X)) :
    finitelyPresentableProperty X B ↔
      ∃ h : qcAlgebraUnderProperty X B, IsFinitePresentation ⟨B, h⟩ :=
  sorry

/-- A bundled quasi-coherent `𝒪_X`-algebra satisfies `finitelyPresentableProperty` if and only
if it is finitely presented. -/
theorem finitelyPresentableProperty_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    finitelyPresentableProperty X A.obj ↔ IsFinitePresentation A :=
  sorry

/-- If `X` is a quasi-compact and quasi-separated algebraic space over a scheme `S`, then every
quasi-coherent `𝒪_X`-algebra is a small filtered colimit of finitely presented quasi-coherent
`𝒪_X`-algebras. -/
theorem finitelyPresentable_ind {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) :
    (finitelyPresentableProperty X).ind.{u} A.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
