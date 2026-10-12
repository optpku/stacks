/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- For a directed inverse system of finite-type scheme morphisms with affine transitions on
quasi-compact, quasi-separated bases and closed-immersion comparison maps, a pointwise
fibre-dimension bound on the induced limit morphism holds at some finite stage. -/
theorem exists_relativeDimensionLE_stage_of_limit_fiberDimensionLE
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (X S : OrderDual I ⥤ Scheme.{u}) (φ : X ⟶ S)
    (cX : Cone X) (hcX : IsLimit cX) (cS : Cone S) (hcS : IsLimit cS)
    [∀ i : I, CompactSpace (S.obj i)]
    [∀ i : I, QuasiSeparatedSpace (S.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (S.map (homOfLE hii'))]
    [∀ i : I, Scheme.Hom.FiniteType (φ.app i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion
      (pullback.lift (X.map (homOfLE hii')) (φ.app i') (φ.naturality (homOfLE hii')))]
    (f : cX.pt ⟶ cS.pt)
    (hf : ∀ i : I, cX.π.app i ≫ φ.app i = f ≫ cS.π.app i)
    (d : ℕ) (hfdim : ∀ x : cX.pt, f.fiberDimensionAt x ≤ (d : WithBot ℕ∞)) :
    ∃ i : I, Scheme.Hom.RelativeDimensionLE (φ.app i) d := sorry

end AlgebraicGeometry.Scheme.Limit
