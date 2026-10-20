module

public import ReasLib.AlgebraicGeometry.BivariantClass.Dedekind
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set
open AlgebraicGeometry
open scoped Classical

noncomputable section

universe u

/-
Lemma 42.63.2: for a pure one-dimensional locally Dedekind base `S` and a
scheme `X` locally of finite type over `S`, capping with `[S]₁` canonically
identifies degree-`p` bivariant classes for `X ⟶ S` with `CH_(1 - p)(X)`.
The explicit pure-dimension-one hypothesis records the intended setup needed
for the degree-one fundamental-class identification; the literal Dedekind-domain
wording also permits fields, where this degree shift is not the stated one.
-/
@[stacks 0FC5] #check (AlgebraicGeometry.BivariantClass.Dedekind.chowEquiv :
  {S : Scheme.{u}} → [UniversallyCatenary S] →
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)] →
    (δ : S → ℤ) → [IsDimensionFunction δ] →
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1) →
    (h_dim : ∀ component : irreducibleComponents S,
      topologicalKrullDim component = 1) →
    (X : Over S) → [LocallyOfFiniteType X.hom] → (p : ℤ) →
      BivariantClass δ (AlgebraicGeometry.BivariantClass.Dedekind.baseMap X) p ≃
        RelativeChow δ X (1 - p))
