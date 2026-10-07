module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty
public import stacks_project.Chap87.Definition_87_11_1_Formal
public import stacks_project.Chap87.Lemma_87_2_1_Size
public import stacks_project.Chap87.Remark_87_9_8_Comparison

/-!
# Remark 87.11.4

Modulo size, and with terminal base `Spec(ℤ)`, the functor of points of an
EGA formal scheme is a fully faithful embedding into fppf sheaves, and lands
in formal algebraic spaces.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

/-- Remark 87.11.4. Modulo set-theoretic issues encoded by a `Sch_α` site `h𝒮`
and a size bound `hsize`, and with terminal base `Spec(ℤ)` encoded by
`hS : IsTerminal (𝒮.toScheme.obj S)`, the functor of points
`sheafOfPoints 𝒮 S` is a fully faithful embedding of EGA formal schemes into
fppf sheaves. For any formal scheme `X`, an affine open covering yields affine
formal algebraic space charts `(sheafOfPoints 𝒮 S).obj Xᵢ` whose maps into
`(sheafOfPoints 𝒮 S).obj X` are representable open immersions, hence
`(sheafOfPoints 𝒮 S).obj X` is a formal algebraic space. Thus EGA formal
schemes are equivalent to a full subcategory of formal algebraic spaces, not
to all of them. -/
@[stacks 0AIR]
theorem isFormalAlgebraicSpace_sheafOfPoints
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : FormalScheme.{u})
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) :
    IsFormalAlgebraicSpace ((sheafOfPoints 𝒮 S).obj X) :=
  sorry

end AlgebraicGeometry.FormalScheme
