module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.RestrictionMaps

/-!
# A small, fixed coordinate family over the original perfect input

Arbitrary module carriers make the type of all DivisorComplexCharts large.
Here every term is the specified finite coordinate module `Fin (rank n) → R`.
Consequently the entire index lives in the universe of the base scheme, which
is necessary to glue without enlarging the universe of the output scheme.
No coordinate chart is selected from the remaining cover theorem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

/-- Small coordinate data: actual finite ranks and linear differentials. -/
structure CoordinateComplex (R : Type u) [CommRing R] where
  rank : ℤ → ℕ
  differential : ∀ i j : ℤ, (Fin (rank i) → R) →ₗ[R] (Fin (rank j) → R)
  shape : ∀ i j, ¬ (ComplexShape.up ℤ).Rel i j → differential i j = 0
  squareZero : ∀ i j k, (differential j k).comp (differential i j) = 0

namespace CoordinateComplex

/-- The complex is constructed on these coordinate modules, not selected by existence. -/
def toComplex {R : Type u} [CommRing R] (A : CoordinateComplex R) :
    CochainComplex (ModuleCat R) ℤ where
  X i := ModuleCat.of R (Fin (A.rank i) → R)
  d i j := ModuleCat.ofHom (A.differential i j)
  shape i j h := by rw [A.shape i j h]; rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    exact A.squareZero i j k

/-- Every term has the actual finite standard basis. -/
theorem finiteFree {R : Type u} [CommRing R] (A : CoordinateComplex R) :
    A.toComplex.IsTermwiseFiniteFree := by
  constructor
  intro i
  change Module.Free R (Fin (A.rank i) → R) ∧ Module.Finite R (Fin (A.rank i) → R)
  exact ⟨inferInstance, inferInstance⟩

theorem differential_apply {R : Type u} [CommRing R] (A : CoordinateComplex R)
    (i j : ℤ) (x : Fin (A.rank i) → R) :
    A.toComplex.d i j x = A.differential i j x := rfl

end CoordinateComplex

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)

/-- All valid *small coordinate* charts subordinate to the original model sieve.
The validity fields are propositions about the fixed coordinate data. -/
structure SmallChart : Type u where
  modelOpen : (modelSieve E hE).Arrow
  U : Y.affineOpens
  subordinate : (U : Y.Opens) ≤ p ⁻¹ᵁ modelOpen.Y
  generator : Γ(Y, U)
  coordinates : CoordinateComplex Γ(Y, U)
  bounded : CochainComplex.bounded (ModuleCat Γ(Y, U)) coordinates.toComplex
  regular : generator ∈ nonZeroDivisors Γ(Y, U)
  ideal_eq : D.ideal U = Ideal.span {generator}
  represents : IsIsomorphic (DerivedCategory.Q.obj coordinates.toComplex)
    ((RingedSpace.moduleDerivedSectionsAtOpen Y.toRingedSpace U).obj
      ((RingedSpace.modulePullbackDerived p.toShHom).obj E))

/-- The actual chart record constructed from the fixed finite coordinate data. -/
def SmallChart.toChart (i : SmallChart E hE p D) : graphChartIndex E p D where
  U := i.U
  generator := i.generator
  model := i.coordinates.toComplex
  bounded := i.bounded
  finiteFree := i.coordinates.finiteFree
  regular := i.regular
  ideal_eq := i.ideal_eq
  represents := i.represents

def SmallChart.toIndex (i : SmallChart E hE p D) : divisorChartIndex E hE p D :=
  ⟨i.toChart, i.modelOpen, i.subordinate⟩

/-- Cover law for this particular coordinate family. Locally trivialize the
finitely many projective terms of the input model and the Cartier equation,
then write their actual differentials in finite standard coordinates.
This is a fixed-family Prop debt, not an existential data-selection API. -/
theorem smallChart_covering [IsEffectiveCartierDivisor D.subschemeι] (y : Y) :
    ∃ i : SmallChart E hE p D, y ∈ (i.U : Y.Opens) := by
  sorry

/-- A cover in the original universe, with only original inputs at entry. -/
def smallChartCover [IsEffectiveCartierDivisor D.subschemeι] : Y.OpenCover :=
  Scheme.Cover.mkOfCovers (SmallChart E hE p D)
    (fun i => (i.U : Y.Opens).toScheme) (fun i => (i.U : Y.Opens).ι)
    (by
      intro y
      obtain ⟨i, hi⟩ := smallChart_covering E hE p D y
      exact ⟨i, ⟨y, hi⟩, rfl⟩)

/-- The Rees piece uses the product ideal of these very coordinate differentials. -/
def smallPiece (i : SmallChart E hE p D) : Scheme.{u} :=
  i.toChart.graphScheme

def smallPieceMap (i : SmallChart E hE p D) : smallPiece E hE p D i ⟶ Y :=
  i.toChart.graphHom

theorem smallChart_model (i : SmallChart E hE p D) :
    i.toChart.model = i.coordinates.toComplex := rfl

theorem smallChart_presentation (i : SmallChart E hE p D) (n : ℤ)
    (x : Fin (i.coordinates.rank n) → Γ(Y, i.U)) :
    CochainComplex.BerthelotOgus.Int.etaPresentationMap
      i.toChart.generator i.toChart.model n x =
        (i.generator • x, i.coordinates.differential n (n + 1) x) := rfl

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
