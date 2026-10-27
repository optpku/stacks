/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Example 27.21.2 (Projective space of a vector space): for a field `k` and a `k`-vector
space `V`, its projective space is `Proj(SymmetricAlgebra k V)`. -/
@[stacks 0FCY] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.scheme :
    ∀ (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V],
      Scheme.{u})

/- In dimension `n + 1`, the projective scheme of a vector space is isomorphic to standard
projective `n`-space. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.nonemptyIsoProjectiveSpaceOfFinrankEq :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] (n : ℕ), Module.finrank k V = n + 1 →
        Nonempty
          (AlgebraicGeometry.ProjectiveSpace.VectorSpace.scheme k V ≅
            AlgebraicGeometry.ProjectiveSpace.scheme k n))

/- The projective scheme of a vector space represents invertible quotients of its associated
module sheaf over `Spec(k)`. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.hasProjectiveBundleRepresentation :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V],
      Nonempty
        (AlgebraicGeometry.Scheme.ProjectiveBundle.Representation
          (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)
          (AlgebraicGeometry.ProjectiveSpace.VectorSpace.moduleSheaf k V)))

/- A `k`-point over `Spec(k)`, expressed as a lift of the identity, is equivalent to a compatible
quotient-isomorphism class of the module sheaf associated to `V`. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.pointEquivQuotient :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      (hP : AlgebraicGeometry.Scheme.ProjectiveBundle.Representation
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.moduleSheaf k V)),
      AlgebraicGeometry.Scheme.ProjectiveBundle.Lift
          (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)
          (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k))) ≃
        CategoryTheory.InvertibleQuotient.IsoClass
          (AlgebraicGeometry.ProjectiveSpace.VectorSpace.moduleSheaf k V))

/- The linear quotient attached to a `k`-point is surjective. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.pointLinearMap_surjective :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      (hP : AlgebraicGeometry.Scheme.ProjectiveBundle.Representation
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.moduleSheaf k V))
      (p : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶
        AlgebraicGeometry.ProjectiveSpace.VectorSpace.scheme k V)
      (hp : p ≫ AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V =
        𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k))),
      Function.Surjective
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.pointLinearMap hP p hp))

/- The target of the quotient attached to a `k`-point is one-dimensional. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.pointLineBundle_finrank_eq_one :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      (hP : AlgebraicGeometry.Scheme.ProjectiveBundle.Representation
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V)
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.moduleSheaf k V))
      (p : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶
        AlgebraicGeometry.ProjectiveSpace.VectorSpace.scheme k V)
      (hp : p ≫ AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V =
        𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k))),
      Module.finrank k
        (AlgebraicGeometry.Scheme.Hom.globalSectionsMod
          (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k)))
          (AlgebraicGeometry.ProjectiveSpace.VectorSpace.pointLineBundle hP p hp)) = 1)

/- A generating linear map to the sections of an invertible module determines a lift over
`Spec(k)`, hence a morphism to the projective scheme of `V`. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.lift :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (L : X.left.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (psi : ModuleCat.of k V ⟶ AlgebraicGeometry.Scheme.Hom.globalSectionsMod X.hom L)
      (hpsi : AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L psi),
      AlgebraicGeometry.Scheme.ProjectiveBundle.Lift
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.toSpec k V) X.hom)

#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.morphism :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (L : X.left.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (psi : ModuleCat.of k V ⟶ AlgebraicGeometry.Scheme.Hom.globalSectionsMod X.hom L)
      (hpsi : AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L psi),
      X.left ⟶ AlgebraicGeometry.ProjectiveSpace.VectorSpace.scheme k V)

/- The canonical construction pulls the fixed actual Serre sheaf O(1) back to L. Both the
comparison morphism and its inverse have explicit local coefficient formulas. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.pullbackTautologicalSheafIso :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (L : X.left.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (psi : ModuleCat.of k V ⟶ AlgebraicGeometry.Scheme.Hom.globalSectionsMod X.hom L)
      (hpsi : AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L psi),
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.morphism X L psi hpsi)).obj
          (AlgebraicGeometry.ProjectiveSpace.VectorSpace.canonicalTautologicalSheaf
            (k := k) (V := V)) ≅ L)

/- The actual canonical section v/1 is carried to psi(v), fixing the symmetric coordinates. -/
#check @AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.inducedLinearMap_eq
#check @AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.pullbackTautologicalSheafIso_quotient
#check @AlgebraicGeometry.ProjectiveSpace.VectorSpace.CanonicalCoordinates
#check @AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.SuppliedModel.morphism_eq_canonical

/- A generating subspace of global sections induces the corresponding projective morphism. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.subspaceMorphism :
    ∀ {k : Type u} [Field k]
      (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (L : X.left.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (W : Submodule k (AlgebraicGeometry.Scheme.Hom.globalSectionsMod X.hom L))
      (hW : AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L
        (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype)),
      X.left ⟶ AlgebraicGeometry.ProjectiveSpace.VectorSpace.scheme k W)

/- A chosen basis identifies the induced morphism with the corresponding homogeneous-coordinate
morphism and gives the commutative comparison diagram. -/
#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.basisMorphism_spec :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
      (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (L : X.left.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (psi : ModuleCat.of k V ⟶ AlgebraicGeometry.Scheme.Hom.globalSectionsMod X.hom L)
      (hpsi : AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L psi),
      AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.BasisMorphismSpec
        n b X L psi
          (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.basisMorphism
            n b X L psi hpsi))

#check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.morphism_basisComparison :
    ∀ {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
      (n : ℕ) (b : Module.Basis (Fin (n + 1)) k V)
      (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (L : X.left.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (psi : ModuleCat.of k V ⟶ AlgebraicGeometry.Scheme.Hom.globalSectionsMod X.hom L)
      (hpsi : AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.Generates X L psi),
      AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.morphism X L psi hpsi ≫
          AlgebraicGeometry.ProjectiveSpace.VectorSpace.basisComparison n b =
        AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem.basisMorphism
          n b X L psi hpsi)
