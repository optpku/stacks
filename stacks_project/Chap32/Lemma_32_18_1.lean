module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.RelativeDimension
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.18.1: for a directed inverse system of finite-type morphisms of schemes with affine
base transitions, quasi-compact and quasi-separated bases, and closed-immersion comparison maps,
a fibre-dimension bound for the induced limit morphism holds at some finite stage. -/
@[stacks 05M5] #check
  (AlgebraicGeometry.Scheme.Limit.exists_relativeDimensionLE_stage_of_limit_fiberDimensionLE :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
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
      (d : ℕ) (hfdim : ∀ x : cX.pt, f.fiberDimensionAt x ≤ (d : WithBot ℕ∞)),
      ∃ i : I, Scheme.Hom.RelativeDimensionLE (φ.app i) d)
