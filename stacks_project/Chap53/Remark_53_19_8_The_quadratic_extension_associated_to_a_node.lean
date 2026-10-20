module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.NodalLocalRing
public import ReasLib.RingTheory.LocalRing.Nodal

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

/- Remark 53.19.8 (The quadratic extension associated to a node) -/
@[stacks 0CBT] #check
  (NodalLocalRing.quadraticAlgebra_spec :
    ∀ (k : Type u) [Field k]
      (A : Type u) [CommRing A] [IsLocalRing A] [Algebra k A] [IsNodalLocalRing A]
      [Algebra.IsSeparableOver k (ResidueField A)],
    Module.finrank (ResidueField A) (NodalLocalRing.quadraticAlgebra A) = 2 ∧
      Algebra.IsSeparable (ResidueField A) (NodalLocalRing.quadraticAlgebra A))

#check
  (NodalLocalRing.quadraticPresentation_equiv :
    ∀ (k : Type u) [Field k]
      (A : Type u) [CommRing A] [IsLocalRing A] [Algebra k A] [IsNodalLocalRing A]
      [Algebra.IsSeparableOver k (ResidueField A)]
      (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))
      (a b c : ResidueField A) (ha : a ≠ 0) (h_discriminant : 4 * a * c - b ^ 2 ≠ 0)
      (h_relation :
        idealConormalAlgebraQuotient (maximalIdeal A)
            (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
              b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
                SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
              c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0),
    Nonempty
      (AdjoinRoot (C a * X ^ 2 + C b * X + C c) ≃ₐ[ResidueField A]
        NodalLocalRing.quadraticAlgebra A))

#check
  (NodalLocalRing.normalizationFiber_equiv :
    ∀ (k : Type u) [Field k]
      (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
      [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)],
    Nonempty
      (NodalLocalRing.quadraticAlgebra A ≃ₐ[ResidueField A]
        (maximalIdeal A).Fiber (Normalization.normalizationRing A)))

#check
  (NodalLocalRing.associatedGradedProj_iso :
    ∀ (k : Type u) [Field k]
      (A : Type u) [CommRing A] [IsCompleteLocalRing A] [Algebra k A]
      [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)],
    Proj (Ideal.AssociatedGraded.grade (maximalIdeal A)) ≅
      Spec (CommRingCat.of (NodalLocalRing.quadraticAlgebra A)))

#check
  (NodalLocalRing.normalizationFiber_iso_specQuadraticAlgebra :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsLocallyNoetherian X.left]
      (x : X.left) [IsNodalLocalRing (stalkRing X x)]
      [Algebra.IsSeparableOver k (ResidueField (stalkRing X x))],
    Nonempty
      (Spec (CommRingCat.of (NodalLocalRing.quadraticAlgebra (stalkRing X x))) ≅
        Scheme.Hom.fiber (Scheme.normalizationTo X.left) x))
