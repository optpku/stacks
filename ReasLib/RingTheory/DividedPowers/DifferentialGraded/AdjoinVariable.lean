module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.ChainAlgebra
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.AdjoinVariable

/-!
# Adjoining a variable to a divided-power chain DGA

This file packages a one-cell extension by its relative mapping property inside the category of
nonnegative strictly commutative chain DGAs with compatible divided powers.  The odd and even
refinements record only the parity of the adjoined degree.  Their coefficient presentations are
derived canonically by comparison with the explicit predifferential models, so an extension never
stores several potentially incoherent coordinate systems.

The differential is therefore never represented by an ordinary ungraded derivation: it is the
differential of an actual `DividedPowerChainAlgebra`, the base inclusion is an actual chain-DGA
homomorphism, and comparison maps preserve multiplication, differentials, and divided powers.

The universal property is therefore the single data owner.  Model-specific files expose the
canonical coefficient equivalences and prove that they preserve multiplication, differential,
the base inclusion, the generator, and divided powers.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DividedPowerChainAlgebra

variable {R : Type u} [CommRing R]

namespace Adjoin

/-- A homogeneous element in degree one below `d` is closed in the underlying chain complex. -/
def IsCycle (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) : Prop :=
  A.toChainDGAlgebra.d (((d : ℕ) - 1 : ℕ) : ℤ) f = 0

namespace IsCycle

variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-- A closed nonnegative homogeneous element, bundled in the canonical cycle object of the
underlying chain DGA. -/
@[stacks 09PM "bundled attaching cycle"]
def toCycle (h : IsCycle A d f) :
    A.toChainDGAlgebra.cycles ((((d : ℕ) - 1 : ℕ) : ℤ)) :=
  A.toChainDGAlgebra.toChainComplex.cyclesMk f
    (((((d : ℕ) - 1 : ℕ) : ℤ)) - 1)
    (ChainComplex.next ℤ (((d : ℕ) - 1 : ℕ))) h

/-- The homogeneous value underlying the bundled cycle is the original attaching element. -/
@[simp, stacks 09PM "underlying value of a bundled attaching cycle"]
theorem iCycles_toCycle (h : IsCycle A d f) :
    A.toChainDGAlgebra.iCycles ((((d : ℕ) - 1 : ℕ) : ℤ)) h.toCycle = f := sorry

end IsCycle

/-- A relative one-cell extension of `A` killing the cycle `f`.  Its mapping property says that a
map out of the extension is exactly a map out of `A` together with a degree-`d` element whose
differential is the image of `f`. -/
@[stacks 09PM "divided-power chain-DGA cell"]
structure Cell (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) where
  /-- The attaching element is closed in the base chain DGA. -/
  attaching_isCycle : IsCycle A d f
  /-- The extended divided-power chain DGA. -/
  algebra : DividedPowerChainAlgebra.{u, v} R
  /-- The canonical inclusion of the base DGA. -/
  ι : A ⟶ algebra
  /-- The adjoined homogeneous variable of degree `d`. -/
  generator : algebra.toChainDGAlgebra.nonnegativePiece (d : ℕ)
  /-- The defining differential equation `dT = f`. -/
  map_generator :
    algebra.toChainDGAlgebra.nonnegativeDifferential d generator =
      ι.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f
  /-- The relative lift determined by the image of the adjoined variable. -/
  lift {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
      (x : C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
      (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
        g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    algebra ⟶ C
  /-- The relative lift restricts to the prescribed map on `A`. -/
  lift_base {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
      (x : C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
      (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
        g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    ι ≫ lift g x hx = g
  /-- The relative lift sends `T` to the prescribed homogeneous element. -/
  lift_generator {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
      (x : C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
      (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
        g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    (lift g x hx).toChainHom ((d : ℕ) : ℤ) generator = x
  /-- Maps out of the cell are determined by their restriction to `A` and their value on `T`. -/
  hom_ext {C : DividedPowerChainAlgebra.{u, v} R} (g h : algebra ⟶ C)
      (hbase : ι ≫ g = ι ≫ h)
      (hgenerator :
        g.toChainHom ((d : ℕ) : ℤ) generator = h.toChainHom ((d : ℕ) : ℤ) generator) :
    g = h

namespace Cell

variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-- The attaching element of a cell, bundled as a cycle in degree `d - 1`. -/
@[stacks 09PM "cell attaching cycle"]
def attachingCycle (X : Cell A d f) :
    A.toChainDGAlgebra.cycles ((((d : ℕ) - 1 : ℕ) : ℤ)) :=
  X.attaching_isCycle.toCycle

/-- The homogeneous value underlying a cell's attaching cycle is its attaching element. -/
@[simp, stacks 09PM "underlying value of a cell attaching cycle"]
theorem iCycles_attachingCycle (X : Cell A d f) :
    A.toChainDGAlgebra.iCycles ((((d : ℕ) - 1 : ℕ) : ℤ)) X.attachingCycle = f := sorry

/-- A morphism out of a cell has the prescribed restriction to the base and value on the
adjoined variable. -/
structure IsLift (X : Cell A d f) {C : DividedPowerChainAlgebra.{u, v} R}
    (g : A ⟶ C) (x : C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (h : X.algebra ⟶ C) : Prop where
  /-- The morphism restricts to the prescribed map on the base. -/
  base : X.ι ≫ h = g
  /-- The morphism sends the adjoined variable to the prescribed element. -/
  generator : h.toChainHom ((d : ℕ) : ℤ) X.generator = x

/-- The canonical relative lift has the prescribed restriction and generator value. -/
theorem lift_isLift (X : Cell A d f) {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    X.IsLift g x (X.lift g x hx) := sorry

/-- A morphism with the prescribed base restriction and generator value is the canonical
relative lift. -/
theorem lift_unique (X : Cell A d f) {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f)
    (h : X.algebra ⟶ C) (hh : X.IsLift g x h) :
    h = X.lift g x hx := sorry

/-- Base data and a compatible image of the adjoined variable admit a unique relative lift. -/
theorem existsUnique_lift (X : Cell A d f) {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    ∃! h : X.algebra ⟶ C, X.IsLift g x h := sorry

/-- A map between two cell models is a comparison when it is the relative lift of the target
base inclusion and target generator. -/
def IsComparison (X Y : Cell A d f) (g : X.algebra ⟶ Y.algebra) : Prop :=
  X.IsLift Y.ι Y.generator g

/-- Being a cell comparison is exactly having the target base restriction and generator value. -/
@[simp]
theorem isComparison_iff (X Y : Cell A d f) (g : X.algebra ⟶ Y.algebra) :
    IsComparison X Y g ↔ X.IsLift Y.ι Y.generator g := sorry

/-- The canonical comparison from one cell model to another, constructed by the relative lift. -/
def comparison (X Y : Cell A d f) : X.algebra ⟶ Y.algebra :=
  X.lift Y.ι Y.generator Y.map_generator

/-- The canonical comparison fixes the base and the adjoined variable. -/
theorem comparison_isComparison (X Y : Cell A d f) :
    IsComparison X Y (X.comparison Y) := sorry

/-- The canonical comparison restricts to the target inclusion on the base cell. -/
@[simp]
theorem ι_comp_comparison (X Y : Cell A d f) :
    X.ι ≫ X.comparison Y = Y.ι := sorry

/-- The canonical comparison sends the source generator to the target generator. -/
@[simp]
theorem comparison_generator (X Y : Cell A d f) :
    (X.comparison Y).toChainHom ((d : ℕ) : ℤ) X.generator = Y.generator := sorry

/-- Every comparison map between two cell models is the canonical comparison. -/
theorem comparison_unique (X Y : Cell A d f) (g : X.algebra ⟶ Y.algebra)
    (hg : IsComparison X Y g) :
    g = X.comparison Y := sorry

/-- There is a unique divided-power chain-DGA comparison between two cell models. -/
theorem existsUnique_comparison (X Y : Cell A d f) :
    ∃! g : X.algebra ⟶ Y.algebra, IsComparison X Y g := sorry

/-- The comparison from a cell model to itself is the identity. -/
@[simp]
theorem comparison_self (X : Cell A d f) :
    X.comparison X = 𝟙 X.algebra := sorry

/-- Canonical cell comparisons compose transitively. -/
@[simp]
theorem comparison_comp (X Y Z : Cell A d f) :
    X.comparison Y ≫ Y.comparison Z = X.comparison Z := sorry

/-- The forward and backward comparisons between two cell models compose to the identity on the
source model. -/
theorem comparison_hom_inv_id (X Y : Cell A d f) :
    X.comparison Y ≫ Y.comparison X = 𝟙 X.algebra := sorry

/-- The backward and forward comparisons between two cell models compose to the identity on the
target model. -/
theorem comparison_inv_hom_id (X Y : Cell A d f) :
    Y.comparison X ≫ X.comparison Y = 𝟙 Y.algebra := sorry

/-- The canonical isomorphism between two realizations of the same divided-power chain-DGA
cell. -/
@[stacks 09PM "canonical cell-model comparison"]
def comparisonIso (X Y : Cell A d f) : X.algebra ≅ Y.algebra where
  hom := X.comparison Y
  inv := Y.comparison X
  hom_inv_id := X.comparison_hom_inv_id Y
  inv_hom_id := X.comparison_inv_hom_id Y

/-- The forward map of the canonical cell-model isomorphism is the canonical comparison. -/
@[simp]
theorem comparisonIso_hom (X Y : Cell A d f) :
    (X.comparisonIso Y).hom = X.comparison Y := sorry

/-- The inverse map of the canonical cell-model isomorphism is the reverse comparison. -/
@[simp]
theorem comparisonIso_inv (X Y : Cell A d f) :
    (X.comparisonIso Y).inv = Y.comparison X := sorry

/-- The canonical isomorphism from a cell model to itself is the identity isomorphism. -/
@[simp]
theorem comparisonIso_self (X : Cell A d f) :
    X.comparisonIso X = Iso.refl X.algebra := sorry

/-- Reversing a canonical cell-model isomorphism exchanges its two models. -/
@[simp]
theorem comparisonIso_symm (X Y : Cell A d f) :
    (X.comparisonIso Y).symm = Y.comparisonIso X := sorry

/-- Canonical cell-model isomorphisms compose transitively. -/
@[simp]
theorem comparisonIso_trans (X Y Z : Cell A d f) :
    (X.comparisonIso Y).trans (Y.comparisonIso Z) = X.comparisonIso Z := sorry

namespace Comparison

/-- The underlying chain maps of the forward and reverse canonical cell comparisons compose to
the identity on the source complex. -/
theorem hom_inv_id (X Y : Cell A d f) :
    (X.comparison Y).toChainHom.toChainMap ≫
        (Y.comparison X).toChainHom.toChainMap =
      𝟙 X.algebra.toChainDGAlgebra.toChainComplex := sorry

/-- The underlying chain maps of the reverse and forward canonical cell comparisons compose to
the identity on the target complex. -/
theorem inv_hom_id (X Y : Cell A d f) :
    (Y.comparison X).toChainHom.toChainMap ≫
        (X.comparison Y).toChainHom.toChainMap =
      𝟙 Y.algebra.toChainDGAlgebra.toChainComplex := sorry

/-- The canonical comparison between two cell models, forgotten to an isomorphism of their
underlying chain complexes. -/
@[stacks 09PM "underlying chain-complex comparison of cell models"]
def chainIso (X Y : Cell A d f) :
    X.algebra.toChainDGAlgebra.toChainComplex ≅
      Y.algebra.toChainDGAlgebra.toChainComplex where
  hom := (X.comparison Y).toChainHom.toChainMap
  inv := (Y.comparison X).toChainHom.toChainMap
  hom_inv_id := hom_inv_id X Y
  inv_hom_id := inv_hom_id X Y

/-- The forward map of the underlying chain-complex comparison is the canonical cell
comparison. -/
@[simp]
theorem chainIso_hom (X Y : Cell A d f) :
    (chainIso X Y).hom = (X.comparison Y).toChainHom.toChainMap := sorry

/-- The inverse map of the underlying chain-complex comparison is the reverse cell
comparison. -/
@[simp]
theorem chainIso_inv (X Y : Cell A d f) :
    (chainIso X Y).inv = (Y.comparison X).toChainHom.toChainMap := sorry

/-- The underlying chain-complex comparison from a cell model to itself is the identity. -/
@[simp]
theorem chainIso_self (X : Cell A d f) :
    chainIso X X = Iso.refl X.algebra.toChainDGAlgebra.toChainComplex := sorry

/-- Reversing an underlying chain-complex comparison exchanges its two cell models. -/
@[simp]
theorem chainIso_symm (X Y : Cell A d f) :
    (chainIso X Y).symm = chainIso Y X := sorry

/-- Underlying chain-complex comparisons compose transitively. -/
@[simp]
theorem chainIso_trans (X Y Z : Cell A d f) :
    (chainIso X Y).trans (chainIso Y Z) = chainIso X Z := sorry

/-- The underlying chain-complex comparison intertwines the two base inclusions. -/
@[stacks 09PM "base naturality of the cell-model chain comparison"]
theorem inclusion_comp_chainIso_hom (X Y : Cell A d f) :
    X.ι.toChainHom.toChainMap ≫ (chainIso X Y).hom =
      Y.ι.toChainHom.toChainMap := sorry

end Comparison

end Cell

namespace Implementation

/-- The zero exponent has admissible weight in every homogeneous coefficient piece. -/
theorem zeroWeightLe (d m : ℕ) : 0 * d ≤ m := sorry

/-- The degree of a coefficient at exponent zero is unchanged. -/
theorem zeroCoefficientDegree (d m : ℕ) : m = m - 0 * d := sorry

/-- The exponent-one weight is admissible in the degree of the variable. -/
theorem oneWeightLe (d : ℕ) : 1 * d ≤ d := sorry

/-- The coefficient of the degree-`d` variable at exponent one lies in base degree zero. -/
theorem oneCoefficientDegree (d : ℕ) : 0 = d - 1 * d := sorry

end Implementation

namespace Odd

/-- The constant coefficient in the degree-`m` odd-variable model. -/
def baseCoeff (A : NonnegGradedAlgebra R) (d m : ℕ) (x : A.piece m) :
    NonnegGradedAlgebra.Adjoin.Odd.Piece A d m :=
  DFinsupp.single ⟨(0 : Fin 2), Implementation.zeroWeightLe d m⟩
    (A.pieceCast (Implementation.zeroCoefficientDegree d m) x)

/-- The coefficient vector representing the odd variable in degree `d`. -/
def generatorCoeff (A : NonnegGradedAlgebra R) (d : ℕ) :
    NonnegGradedAlgebra.Adjoin.Odd.Piece A d d :=
  DFinsupp.single ⟨(1 : Fin 2), Implementation.oneWeightLe d⟩
    (A.pieceCast (Implementation.oneCoefficientDegree d) GradedMonoid.GOne.one)

/-- An odd one-cell extension attached along a closed homogeneous element.  Its coefficient
presentation is derived canonically from the cell universal property rather than stored as
independent data. -/
@[stacks 09PM "odd one-cell extension"]
structure Extension (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) extends Cell A d f where
  /-- The degree of the exterior variable is odd. -/
  degree_odd : Odd (d : ℕ)

namespace Extension

variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

end Extension

end Odd

namespace Even

/-- The constant coefficient in the degree-`m` even-variable model. -/
def baseCoeff (A : NonnegGradedAlgebra R) (d m : ℕ) (x : A.piece m) :
    NonnegGradedAlgebra.Adjoin.Even.Piece A d m :=
  DFinsupp.single ⟨0, Implementation.zeroWeightLe d m⟩
    (A.pieceCast (Implementation.zeroCoefficientDegree d m) x)

/-- The coefficient vector representing the even variable in degree `d`. -/
def generatorCoeff (A : NonnegGradedAlgebra R) (d : ℕ) :
    NonnegGradedAlgebra.Adjoin.Even.Piece A d d :=
  DFinsupp.single ⟨1, Implementation.oneWeightLe d⟩
    (A.pieceCast (Implementation.oneCoefficientDegree d) GradedMonoid.GOne.one)

/-- An even one-cell extension attached along a closed homogeneous element.  Its divided-monomial
coordinates are derived canonically from the cell universal property rather than stored as
independent data. -/
@[stacks 09PM "even one-cell extension"]
structure Extension (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) extends Cell A d f where
  /-- The degree of the divided-power variable is even. -/
  degree_even : Even (d : ℕ)

namespace Extension

variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

end Extension

end Even

end Adjoin

end DividedPowerChainAlgebra
