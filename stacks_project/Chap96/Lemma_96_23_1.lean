module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_4_3_Sheaf
public import stacks_project.Chap96.«96_9_4_1_Comparison»
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh

/-!
# Locally quasi-coherent modules with fppf comparison are fppf sheaves

A locally quasi-coherent étale module on an algebraic stack is an fppf sheaf
when the comparison `c_φ` of 96.9.4.1 is an isomorphism along morphisms lying
over flat, locally of finite presentation maps of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 96.23.1: if `X` is an algebraic stack over `S` and `F` is a locally
quasi-coherent étale `𝒪_X`-module such that `moduleComparison φ F` is an
isomorphism whenever `φ` lies over a flat and locally of finite presentation
morphism of schemes, then `F` is a sheaf for the fppf topology. -/
@[stacks 076T]
theorem isSheaf_fppf_of_isLocallyQuasiCoherent
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : ∀ {x y : X.total} (φ : x ⟶ y),
      Flat (X.p.map φ).left → LocallyOfFinitePresentation (X.p.map φ).left →
        IsIso (moduleComparison φ F)) :
    Presheaf.IsSheaf X.fppfTopology F.val.presheaf :=
  sorry

/-- Under the hypotheses of `isSheaf_fppf_of_isLocallyQuasiCoherent`, `F` is a
sheaf for the associated fppf site of `X` in the sense of
`FiberedInGroupoids.IsSheafFor`. -/
theorem isSheafFor_fppf_of_isLocallyQuasiCoherent
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F]
    (h_comparison : ∀ {x y : X.total} (φ : x ⟶ y),
      Flat (X.p.map φ).left → LocallyOfFinitePresentation (X.p.map φ).left →
        IsIso (moduleComparison φ F)) :
    FiberedInGroupoids.IsSheafFor X.p StandardTopology.fppf F.val.presheaf :=
  sorry

end AlgebraicGeometry.GroupoidsOver
