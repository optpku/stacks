/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import ReasLib.AlgebraicGeometry.Scheme.BigZariski.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.TheoremOfCube
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Curve.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Torsion
public import ReasLib.Topology.Sober.GenericPoint
import StacksCheckRecall

@[expose] public section

universe u w

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

section

variable (X : Scheme.{u})

/- Exercise 111.66.2 (Theorems) (1): a scheme is T0 and QuasiSober, so every
irreducible closed subset of its underlying space has a unique generic point. -/
@[stacks 0H8R] #check
  (TopologicalSpace.IsIrreducible.existsUnique_isGenericPoint :
    ∀ {Z : Set X}, IsIrreducible Z → IsClosed Z → ∃! x : X, IsGenericPoint x Z)

/- Exercise 111.66.2 (Theorems) (2): a Zariski sheaf of types on schemes is
representable if it is covered by a jointly surjective family of relatively
representable open immersions from representable functors. -/
@[stacks 0H8R] #check
  (AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_locallySurjective_subfunctors :
    ∀ (F : Sheaf Scheme.zariskiTopology.{u} (Type u))
      {I : Type w} [Small.{u} I]
      (H : I → CategoryTheory.Subfunctor F.obj)
      (h_open : ∀ i, IsOpenImmersion.presheaf (H i).ι)
      (h_representable : ∀ i, (H i).toFunctor.IsRepresentable)
      (h_locallySurjective : Presheaf.IsLocallySurjective Scheme.zariskiTopology
        (Limits.Sigma.desc (fun i ↦ (H i).ι))),
      F.obj.IsRepresentable)

/- Exercise 111.66.2 (Theorems) (3): the relative Picard functor of a smooth
projective curve over a separably closed field is representable; this includes
the algebraically closed case, since IsAlgClosed implies IsSepClosed. -/
@[stacks 0H8R] #check
  (AlgebraicGeometry.RelativePicard.functor_isRepresentable_of_smoothProjectiveCurve :
    ∀ {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
      [Smooth X.hom] [Projective X.hom],
      (RelativePicard.functor X).obj.IsRepresentable)

/- Exercise 111.66.2 (Theorems) (4): if `1 ≤ n` is invertible in an algebraically
closed field `k`, the `n`-torsion in the Picard group of a smooth projective
curve `X` is additively equivalent to `2 * genus X` copies of `ZMod n`. -/
@[stacks 0H8R] #check
  (AlgebraicGeometry.Curve.picardTorsionEquiv :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Smooth X.hom] [Projective X.hom] (n : ℕ),
      1 ≤ n → IsUnit (n : k) →
        Nonempty
          (AddSubgroup.torsionBy X.left.PicardGroup (n : ℤ) ≃+
            (Fin (2 * Curve.genus X) → ZMod n)))

/- Exercise 111.66.2 (Theorems) (5): theorem of the cube: an invertible module on
`X ×[S] Y ×[S] Z` is trivial if its two section-face restrictions and one
`Z`-fibre restriction are trivial. This specializes to a triple product of
smooth projective varieties over an algebraically closed field with k-points. -/
@[stacks 0H8R] #check
  (AlgebraicGeometry.Scheme.Modules.Invertible.isTrivial_of_cube :
    ∀ {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (k : Z ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      [GeometricallyIntegral f] [Flat g] [IsProper g]
      [Scheme.Hom.FinitePresentation g] [GeometricallyIntegral g] [ConnectedSpace Z]
      (x : SplitEpi f) (y : SplitEpi g) (z : Z)
      (L : (pullback (pullback.fst f g ≫ f) k).Modules)
      [Scheme.Modules.Invertible L],
      RingedSpace.IsTrivial
        ((Scheme.Modules.pullback (Scheme.TripleProduct.firstSection f g k x)).obj L) →
      RingedSpace.IsTrivial
        ((Scheme.Modules.pullback (Scheme.TripleProduct.secondSection f g k y)).obj L) →
      RingedSpace.IsTrivial
        ((Scheme.Modules.pullback
          ((pullback.snd (pullback.fst f g ≫ f) k).fiberι z)).obj L) →
      RingedSpace.IsTrivial L)

end
