/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.IrreducibleFibers
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Exercise 111.52.5 (1): a reduced projective scheme over a field mapping to the
projective line with nonempty irreducible fibres of dimension `d` has dimension `d + 1`. -/
@[stacks 02B0] #check
  (AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_succ_of_irreducibleFibers :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
      {f : X ⟶ ProjectiveSpace.scheme k 1}
      (h_projective : ∃ (n : ℕ) (embedding : X ⟶ ProjectiveSpace.scheme k n),
        IsClosedImmersion embedding ∧
          embedding ≫ ProjectiveSpace.toSpec k n = X ↘ Spec (CommRingCat.of k))
      (hf : f ≫ ProjectiveSpace.toSpec k 1 = X ↘ Spec (CommRingCat.of k))
      {d : ℕ} (h_irr : ∀ t, IrreducibleSpace (f.fiber t))
      (h_dim : ∀ t, topologicalKrullDim (f.fiber t) = (d : WithBot ℕ∞)),
      topologicalKrullDim X = (d + 1 : WithBot ℕ∞))

/- Exercise 111.52.5 (2): every fibre of an irreducible component of dimension
`d + 1` has dimension `d`. -/
@[stacks 02B0] #check
  (AlgebraicGeometry.Scheme.Hom.fiber_topologicalKrullDim_irreducibleComponent :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
      {f : X ⟶ ProjectiveSpace.scheme k 1}
      (h_projective : ∃ (n : ℕ) (embedding : X ⟶ ProjectiveSpace.scheme k n),
        IsClosedImmersion embedding ∧
          embedding ≫ ProjectiveSpace.toSpec k n = X ↘ Spec (CommRingCat.of k))
      (hf : f ≫ ProjectiveSpace.toSpec k 1 = X ↘ Spec (CommRingCat.of k))
      {d : ℕ} (h_irr : ∀ t, IrreducibleSpace (f.fiber t))
      (h_dim : ∀ t, topologicalKrullDim (f.fiber t) = (d : WithBot ℕ∞))
      (X0 : irreducibleComponents X)
      (hX0 : topologicalKrullDim (X.irreducibleComponentSubscheme X0) =
        (d + 1 : WithBot ℕ∞)) (t : ProjectiveSpace.scheme k 1),
      topologicalKrullDim ((X.irreducibleComponentSubschemeι X0 ≫ f).fiber t) =
        (d : WithBot ℕ∞))

/- Exercise 111.52.5 (3): the component fibre fills the original fibre topologically. -/
@[stacks 02B0] #check
  (AlgebraicGeometry.Scheme.Hom.surjective_compFiberToBaseFiber_irreducibleComponent :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
      {f : X ⟶ ProjectiveSpace.scheme k 1}
      (h_projective : ∃ (n : ℕ) (embedding : X ⟶ ProjectiveSpace.scheme k n),
        IsClosedImmersion embedding ∧
          embedding ≫ ProjectiveSpace.toSpec k n = X ↘ Spec (CommRingCat.of k))
      (hf : f ≫ ProjectiveSpace.toSpec k 1 = X ↘ Spec (CommRingCat.of k))
      {d : ℕ} (h_irr : ∀ t, IrreducibleSpace (f.fiber t))
      (h_dim : ∀ t, topologicalKrullDim (f.fiber t) = (d : WithBot ℕ∞))
      (X0 : irreducibleComponents X)
      (hX0 : topologicalKrullDim (X.irreducibleComponentSubscheme X0) =
        (d + 1 : WithBot ℕ∞)) (t : ProjectiveSpace.scheme k 1),
      Surjective (AlgebraicGeometry.Scheme.Hom.compFiberToBaseFiber
        (X.irreducibleComponentSubschemeι X0) f t))

/- The component fibres and original fibres have the same underlying subsets of `X`. -/
#check
  (AlgebraicGeometry.Scheme.Hom.range_fiberι_irreducibleComponent_eq :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
      {f : X ⟶ ProjectiveSpace.scheme k 1}
      (h_projective : ∃ (n : ℕ) (embedding : X ⟶ ProjectiveSpace.scheme k n),
        IsClosedImmersion embedding ∧
          embedding ≫ ProjectiveSpace.toSpec k n = X ↘ Spec (CommRingCat.of k))
      (hf : f ≫ ProjectiveSpace.toSpec k 1 = X ↘ Spec (CommRingCat.of k))
      {d : ℕ} (h_irr : ∀ t, IrreducibleSpace (f.fiber t))
      (h_dim : ∀ t, topologicalKrullDim (f.fiber t) = (d : WithBot ℕ∞))
      (X0 : irreducibleComponents X)
      (hX0 : topologicalKrullDim (X.irreducibleComponentSubscheme X0) =
        (d + 1 : WithBot ℕ∞)) (t : ProjectiveSpace.scheme k 1),
      Set.range ((X.irreducibleComponentSubschemeι X0 ≫ f).fiberι t ≫
        X.irreducibleComponentSubschemeι X0) = Set.range (f.fiberι t))

/- Exercise 111.52.5 (4): the reduced projective scheme with these fibres is irreducible. -/
@[stacks 02B0] #check
  (AlgebraicGeometry.Scheme.Hom.irreducibleSpace_of_irreducibleFibers :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
      {f : X ⟶ ProjectiveSpace.scheme k 1}
      (h_projective : ∃ (n : ℕ) (embedding : X ⟶ ProjectiveSpace.scheme k n),
        IsClosedImmersion embedding ∧
          embedding ≫ ProjectiveSpace.toSpec k n = X ↘ Spec (CommRingCat.of k))
      (hf : f ≫ ProjectiveSpace.toSpec k 1 = X ↘ Spec (CommRingCat.of k))
      {d : ℕ} (h_irr : ∀ t, IrreducibleSpace (f.fiber t))
      (h_dim : ∀ t, topologicalKrullDim (f.fiber t) = (d : WithBot ℕ∞)),
      IrreducibleSpace X)
