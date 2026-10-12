/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Properties
public import ReasLib.AlgebraicGeometry.Curve.RiemannHurwitz
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

/- Exercise 111.59.2 (Theorems) (1): pushforward along a quasi-compact quasi-separated
morphism preserves quasi-coherent modules. -/
@[stacks 0DT1] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward.isQuasicoherent :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      (F : X.Modules) [F.IsQuasicoherent],
      ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F).IsQuasicoherent)

/- Exercise 111.59.2 (Theorems) (2): cohomology of a coherent sheaf on a projective variety
over a field is finite over the base; the owner is finiteness of coherent cohomology for a
proper morphism to Spec of a Noetherian ring. -/
@[stacks 0DT1] #check
  (AlgebraicGeometry.Scheme.Hom.cohomologyFinite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (F : X.Modules) [F.IsCoherent] (i : ℕ),
      Module.Finite A (AlgebraicGeometry.Scheme.Hom.cohomology f F i))

/- Exercise 111.59.2 (Theorems) (3): Serre duality for a projective scheme over a field:
morphisms into the dualizing module are identified with the ground-field dual of top-degree
cohomology; the owner applies to proper schemes over a field. -/
@[stacks 0DT1] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleDualityComparison_bijective :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : Scheme.QCoh X),
      Function.Bijective
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleDualityComparison
          f F))

/- Exercise 111.59.2 (Theorems) (4): Riemann–Hurwitz for a finite separable morphism of
smooth proper curves: `2 * gX - 2 = (2 * gY - 2) * deg(f) + deg(R)`, where `R` is the
effective Cartier divisor defined by the Kähler different. -/
@[stacks 0DT1] #check
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
