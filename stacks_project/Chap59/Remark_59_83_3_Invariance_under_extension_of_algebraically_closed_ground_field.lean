module

import StacksCheckRecall
public import ReasLib.Algebra.Polynomial.ArtinSchreier
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.AffineLine
public import stacks_project.Chap59.Lemma_59_83_2

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Remark 59.83.3 (Invariance under extension of algebraically closed ground field)
The Artin–Schreier cokernel computes the first étale cohomology of the affine line. -/
@[stacks 0A47] #check (AlgebraicGeometry.Etale.AffineLine.h1_isIsomorphic_artinSchreierCoker :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p],
    IsIsomorphic
      ((Sheaf.functorH (AlgebraicGeometry.Etale.AffineLine.scheme k).smallEtaleTopology 1).obj
        (CategoryTheory.constantZModSheaf.{_, _, u} (AlgebraicGeometry.Etale.AffineLine.scheme k).smallEtaleTopology p))
      (AddCommGrpCat.of (Polynomial.artinSchreierCoker p k)))

/- Remark 59.83.3 (Invariance under extension of algebraically closed ground field)
Polynomials supported in degrees not divisible by p give unique representatives.
If the field is not algebraically closed, additional constant representatives are needed. -/
@[stacks 0A47] #check (Polynomial.pCoprimeDegree_represents_coker :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p],
    Function.Bijective
      ((QuotientAddGroup.mk' (Polynomial.artinSchreier p k).range).comp
        (Polynomial.pCoprimeDegree p k).subtype))

/- Remark 59.83.3 (Invariance under extension of algebraically closed ground field)
Cohomology need not be invariant under algebraically closed ground-field extension.
By Lemma 59.83.2, this phenomenon is special to p-power torsion in characteristic p;
it does not occur for torsion prime to the characteristic. -/
@[stacks 0A47] #check (AlgebraicGeometry.Etale.AffineLine.h1_baseChange_not_isIso :
    ∀ (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    [Algebra k k'] (p : ℕ) [Fact p.Prime] [CharP k p]
    (h_ne : ¬ Function.Surjective (algebraMap k k')),
    ¬ IsIso
      (AlgebraicGeometry.Scheme.Hom.etaleHq_constant_pullback (AlgebraicGeometry.Etale.AffineLine.mapOfAlgebra k k')
        (AddCommGrpCat.of (ULift.{u} (ZMod p))) 1))

/- Remark 59.83.3 (Invariance under extension of algebraically closed ground field)
The induced map of fundamental groups need not be an isomorphism, so the étale
homotopy type of the affine line depends on the algebraically closed ground field. -/
@[stacks 0A47] #check (AlgebraicGeometry.Etale.AffineLine.pi1_map_not_bijective :
    ∀ (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    [Algebra k k'] (p : ℕ) [Fact p.Prime] [CharP k p]
    [ConnectedSpace (AlgebraicGeometry.Etale.AffineLine.scheme k)] [ConnectedSpace (AlgebraicGeometry.Etale.AffineLine.scheme k')]
    (xbar : GeometricPoint (AlgebraicGeometry.Etale.AffineLine.scheme k'))
    (h_ne : ¬ Function.Surjective (algebraMap k k')),
    ¬ Function.Bijective
      (AlgebraicGeometry.Scheme.GeometricPoint.fundamentalGroupMap
        (AlgebraicGeometry.Etale.AffineLine.mapOfAlgebra k k') xbar))

