/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.Curve.RiemannHurwitz
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties
public import stacks_project.Chap54.Lemma_54_17_1
public import stacks_project.Chap111.Exercise_111_56_2_Results
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Intersection
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

/- Exercise 111.61.2 (Theorems) (1): Riemann–Hurwitz for a finite separable morphism of
smooth proper curves: `2 * gX - 2 = (2 * gY - 2) * deg(f) + deg(R)`, where `R` is the
effective Cartier divisor defined by the Kähler different. -/
@[stacks 0ELH] #check
  (AlgebraicGeometry.Curve.riemannHurwitz :
    ∀ {k : Type u} [Field k] (X Y : SchemeOverField k)
      [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
      [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
      [LocallyOfFiniteType f.left] [IsDominant f.left]
      (h_finite : f.left.FiniteFunctionFieldExtension)
      (h_separable : f.left.SeparableFunctionFieldExtension)
      (hΓX : Function.Bijective (globalSectionsMap X.hom))
      (hΓY : Function.Bijective (globalSectionsMap Y.hom))
      (gX gY : ℕ)
      (h_genusX : gX = genus X (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓX)
      (h_genusY : gY = genus Y (AlgebraicGeometry.topologicalKrullDim_eq_one Y) hΓY),
      2 * (gX : ℤ) - 2 =
        (2 * (gY : ℤ) - 2) * (f.left.inducedFunctionFieldDegree : ℤ) +
          (Module.finrank k
            (globalSectionsAlg (subschemeι (kaehlerDifferent f.left) ≫ X.hom)) : ℤ))

/- Exercise 111.61.2 (Theorems) (2): Clifford's theorem for a special invertible module
on a smooth projective geometrically irreducible curve: twice the zeroth cohomology
finrank is at most the degree plus two. -/
@[stacks 0ELH] #check
  (AlgebraicGeometry.SchemeOverField.clifford :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
      (L : X.left.Modules) [Invertible L]
      (h0 : 0 < cohomologyFinrank X.hom L 0)
      (h1 : 0 < cohomologyFinrank X.hom L 1),
      2 * (cohomologyFinrank X.hom L 0 : ℤ) ≤
        curveDegreeOfInvertible X.hom
          (topologicalKrullDim_eq_one X).le L + 2)

/- Exercise 111.61.2 (Theorems) (3): a proper birational morphism between integral
Noetherian regular schemes of dimension `2` is a finite sequence of blowups at closed
points. -/
@[stacks 0ELH] #check
  (AlgebraicGeometry.Scheme.Hom.exists_pointBlowupSequence :
    ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      [IsIntegral X] [IsIntegral Y] [Scheme.Regular X] [Scheme.Regular Y]
      (f : X ⟶ Y) [IsProper f] [IsBirational f]
      (hX_dim : topologicalKrullDim X = 2) (hY_dim : topologicalKrullDim Y = 2),
      ∃ s : Scheme.PointBlowupSequence Y X, s.toSource = f)

namespace AlgebraicGeometry.Scheme.Modules

/-- Factorwise invertibility of the two-term family `![H, D]`. -/
instance instInvertible_pair {X : Scheme.{u}} (H D : X.Modules)
    [Invertible H] [Invertible D] : ∀ j : Fin 2, Invertible (![H, D] j) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SchemeOverField

/-- Exercise 111.61.2 (Theorems) (4): Hodge index theorem on a smooth projective surface:
if `H` is ample invertible and `D` is invertible with vanishing intersection number against
`H`, then the self-intersection of `D` is nonpositive. -/
@[stacks 0ELH]
theorem hodgeIndex
    {k : Type u} [Field k] (X : SchemeOverField k)
    [ProjectiveVariety X] [SmoothOfRelativeDimension 2 X.hom]
    (hXdim : topologicalKrullDim X.left = 2)
    [HasExt (Sheaf (Opens.grothendieckTopology
      (⊥ : X.left.IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})]
    (H D : X.left.Modules) [Invertible H] [Invertible D] [IsAmple H]
    (hHD : number k X.hom (⊥ : X.left.IdealSheafData)
      (topologicalKrullDim_bot_eq X.left hXdim) ![H, D] = 0) :
    selfNumber k X.hom (⊥ : X.left.IdealSheafData)
      (topologicalKrullDim_bot_eq X.left hXdim) D ≤ 0 := sorry

/-- A scheme locally of finite type and quasi-compact over a finite field has only finitely
many points with values in a finite extension. -/
instance finite_schemeHom_specField
    {k L : Type u} [Field k] [Finite k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    Finite (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ X) := sorry

/-- Exercise 111.61.2 (Theorems) (5): Riemann hypothesis for a smooth projective
geometrically irreducible curve over a finite field: the Hasse–Weil bound
`|#X(L) - q^n - 1| ^ 2 ≤ 4 * g^2 * q^n` for a degree-`n` extension `L / k`. -/
@[stacks 0ELH]
theorem riemannHypothesis_curve
    {k : Type u} [Field k] [Fintype k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (n : ℕ) (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
    (hdeg : Module.finrank k L = n) :
    |(Nat.card (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ X) : ℤ) -
        (Fintype.card k : ℤ) ^ n - 1| ^ 2 ≤
      4 * (Curve.genus X : ℤ) ^ 2 * (Fintype.card k : ℤ) ^ n := sorry

end AlgebraicGeometry.SchemeOverField
