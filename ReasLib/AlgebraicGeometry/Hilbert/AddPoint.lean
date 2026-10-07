module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import ReasLib.AlgebraicGeometry.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback.Sum
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Complement
public import ReasLib.CategoryTheory.RepresentablePresheaf

/-!
# Adding a point to a relative effective divisor

This file constructs addition of Hilbert points, the natural transformation that adds the
graph of a section, and the induced morphism between explicit representing objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Hilbert

variable {S : Scheme.{u}}

/-- The graph of a morphism `x : T ⟶ X` over `S` inside `X ×ₛ T`. -/
def sectionGraph {X T : Over S} (x : T ⟶ X) :
    T.left ⟶ pullback X.hom T.hom :=
  pullback.lift x.left (𝟙 T.left) (x.w.trans (Category.id_comp _).symm)

/-- The first projection of the graph of a morphism is the original morphism. -/
theorem sectionGraph_fst {X T : Over S} (x : T ⟶ X) :
    sectionGraph x ≫ pullback.fst X.hom T.hom = x.left := sorry

/-- The second projection of the graph of a morphism is the identity of its source. -/
theorem sectionGraph_snd {X T : Over S} (x : T ⟶ X) :
    sectionGraph x ≫ pullback.snd X.hom T.hom = 𝟙 T.left := sorry

/-- The ideal sheaf defining the graph of a morphism `x : T ⟶ X` over `S`. -/
def sectionIdeal {X T : Over S} (x : T ⟶ X) :
    (pullback X.hom T.hom).IdealSheafData :=
  (sectionGraph x).ker

/-- The graph ideal is the kernel ideal of the graph morphism. -/
theorem sectionIdeal_def {X T : Over S} (x : T ⟶ X) :
    sectionIdeal x = (sectionGraph x).ker := sorry

/-- The graph ideal on a smooth relative curve is finite locally free of rank one over its base. -/
theorem sectionIdeal_isFiniteLocallyFreeOfRank {X T : Over S}
    [SmoothOfRelativeDimension 1 X.hom] (x : T ⟶ X) :
    IsFiniteLocallyFreeOfRank
      ((sectionIdeal x).subschemeι ≫ pullback.snd X.hom T.hom) 1 := sorry

namespace Point

/-- Regard a morphism `x : T ⟶ X` as the degree-one Hilbert point given by its graph. -/
def ofSection {X T : Over S} [SmoothOfRelativeDimension 1 X.hom]
    (x : T ⟶ X) : Point X 1 T where
  ideal := sectionIdeal x
  finiteLocallyFree := sectionIdeal_isFiniteLocallyFreeOfRank x

/-- The ideal of the Hilbert point associated to a section is its graph ideal. -/
theorem ofSection_ideal {X T : Over S} [SmoothOfRelativeDimension 1 X.hom]
    (x : T ⟶ X) :
    (ofSection x).ideal = sectionIdeal x := sorry

/-- Formation of a section-generated degree-one Hilbert point commutes with base change. -/
theorem ofSection_pullback {X T T' : Over S} [SmoothOfRelativeDimension 1 X.hom]
    (x : T ⟶ X) (h : T' ⟶ T) :
    (ofSection x).pullback h = ofSection (h ≫ x) := sorry

/-- The sum ideal of two Hilbert points has the sum of their finite locally free ranks. -/
theorem add_isFiniteLocallyFreeOfRank {X T : Over S}
    [SmoothOfRelativeDimension 1 X.hom] {d₁ d₂ : ℕ}
    (p : Point X d₁ T) (q : Point X d₂ T) :
    IsFiniteLocallyFreeOfRank
      ((effectiveCartierDivisorSum p.ideal q.ideal).subschemeι ≫
        pullback.snd X.hom T.hom) (d₁ + d₂) := sorry

/-- Add two Hilbert points by summing their effective Cartier divisor ideals. -/
def add {X T : Over S} [SmoothOfRelativeDimension 1 X.hom]
    {d₁ d₂ : ℕ} (p : Point X d₁ T) (q : Point X d₂ T) :
    Point X (d₁ + d₂) T where
  ideal := effectiveCartierDivisorSum p.ideal q.ideal
  finiteLocallyFree := add_isFiniteLocallyFreeOfRank p q

/-- The ideal of a sum of Hilbert points is the effective Cartier divisor sum. -/
theorem add_ideal {X T : Over S} [SmoothOfRelativeDimension 1 X.hom]
    {d₁ d₂ : ℕ} (p : Point X d₁ T) (q : Point X d₂ T) :
    (p.add q).ideal =
      effectiveCartierDivisorSum p.ideal q.ideal := sorry

/-- Addition of Hilbert points commutes with base change. -/
theorem add_pullback {X T T' : Over S} [SmoothOfRelativeDimension 1 X.hom]
    {d₁ d₂ : ℕ} (p : Point X d₁ T) (q : Point X d₂ T) (h : T' ⟶ T) :
    (p.add q).pullback h = (p.pullback h).add (q.pullback h) := sorry

end Point

/-- The pointwise operation sending a Hilbert point and a section to their divisor sum. -/
def addPointApp (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d : ℕ) (T : (Over S)ᵒᵖ)
    (p : (functor X d ⊗ yoneda.obj X).obj T) : Point X (d + 1) T.unop :=
  p.1.add (Point.ofSection p.2)

/-- The pointwise add-point operation is natural in the test scheme. -/
theorem addPointApp_naturality (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d : ℕ) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (functor X d ⊗ yoneda.obj X).map f ≫
        TypeCat.ofHom (addPointApp X d T') =
      TypeCat.ofHom (addPointApp X d T) ≫ (functor X (d + 1)).map f := sorry

/-- The natural transformation `(D, x) ↦ D + x` on Hilbert points. -/
def addPoint (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d : ℕ) : functor X d ⊗ yoneda.obj X ⟶ functor X (d + 1) where
  app T := TypeCat.ofHom (addPointApp X d T)
  naturality := fun _ _ f ↦ addPointApp_naturality X d f

/-- At every test scheme, `addPoint` sends `(D, x)` to `D + x`. -/
theorem addPoint_app (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d : ℕ) (T : (Over S)ᵒᵖ) (p : (functor X d ⊗ yoneda.obj X).obj T) :
    (addPoint X d).app T p = p.1.add (Point.ofSection p.2) := sorry

/-- The morphism of explicit representing objects induced by adding a point. -/
def addPointMapWith (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d : ℕ) {H_d H_succ : Over S}
    (R_d : (functor X d).RepresentableBy H_d)
    (R_succ : (functor X (d + 1)).RepresentableBy H_succ) :
    H_d ⊗ X ⟶ H_succ :=
  (Functor.Monoidal.RepresentableBy.tensorObj R_d
      (Functor.RepresentableBy.yoneda X)).map R_succ (addPoint X d)

/-- The representing equivalence sends `addPointMapWith` to the add-point transformation
applied to the universal pair. -/
theorem addPointMapWith_homEquiv (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    (d : ℕ) {H_d H_succ : Over S}
    (R_d : (functor X d).RepresentableBy H_d)
    (R_succ : (functor X (d + 1)).RepresentableBy H_succ) :
    R_succ.homEquiv (addPointMapWith X d R_d R_succ) =
      (addPoint X d).app (op (H_d ⊗ X))
        ((Functor.Monoidal.RepresentableBy.tensorObj R_d
          (Functor.RepresentableBy.yoneda X)).homEquiv (𝟙 (H_d ⊗ X))) := sorry

/-- The add-point morphism between the chosen representing objects of consecutive Hilbert
functors. -/
def addPointMap (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ) :
    (functor X d).reprX ⊗ X ⟶ (functor X (d + 1)).reprX :=
  addPointMapWith X d (functor X d).representableBy
    (functor X (d + 1)).representableBy

/-- The chosen add-point map is the explicit-representation construction for the chosen
representations. -/
theorem addPointMap_def (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ) :
    addPointMap X d =
      addPointMapWith X d (functor X d).representableBy
        (functor X (d + 1)).representableBy := sorry

/-- Adding a point to a degree-`d` Hilbert scheme is finite locally free of rank `d + 1`. -/
@[instance]
theorem addPointMap_isFiniteLocallyFreeOfRank {S : Scheme.{u}} (X : Over S)
    [SmoothOfRelativeDimension 1 X.hom]
    [∀ n : ℕ, (functor X n).IsRepresentable] (d : ℕ) :
    IsFiniteLocallyFreeOfRank (addPointMap X d).left (d + 1) := sorry

end AlgebraicGeometry.Hilbert
