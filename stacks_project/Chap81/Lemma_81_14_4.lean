module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.FiniteFlatQuotient

/-!
# Finite-flat quotients of étale local rings after admissible blowups

A proper morphism of qcqs algebraic spaces that is étale along a closed
subspace of a quasi-compact open, and an isomorphism onto its image there,
has, after a `V`-admissible blowup, a strict transform whose étale local
rings along the closure of that subspace admit a finite flat quotient from
the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace StrictTransform

/- Lemma 81.14.4. Let `S` be a scheme. Let `f : X ⟶ Y` be a proper morphism of
quasi-compact and quasi-separated algebraic spaces over `S`. Let `V ⊂ Y` be a
quasi-compact open and write `U = f⁻¹(V)` for `(V.inverseImage f).X`, so
`f|_U = restrictTo f V`. Let `A ⊂ U` and `B ⊂ V` be closed subspaces,
with `φ : A.X ⟶ B.X` the restriction `f|_A`, an isomorphism, and assume `f` is
étale at every point of `A`. Then there exists a `V`-admissible blowing up
`b : Y' ⟶ Y` such that the strict transform `f' : X' ⟶ Y'` satisfies: for every
geometric point `ā` of the closure of `|A|` in `|X'|` there exists an ideal `I`
of `etaleLocalRing X' ā` whose quotient map `Ideal.Quotient.mk I` realises a
quotient `𝒪_{X', ā} ⟶ 𝒪` for which the composite
`etaleLocalRing Y' (ā.map f') →+* 𝒪` is a finite flat local homomorphism
onto a nonzero quotient. -/
@[stacks 0F48] #check
  (AlgebraicGeometry.AlgebraicSpace.StrictTransform.exists_blowup_finiteFlatStalkQuotient :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f]
    (V : OpenSubspace Y) [QuasiCompact V.ι]
    [IsQuasiCompact V.X] [IsAbsolutelyQuasiSeparated V.X]
    [IsQuasiCompact ((V.inverseImage f).X)]
    [IsAbsolutelyQuasiSeparated ((V.inverseImage f).X)]
    (A : ClosedSubspace ((V.inverseImage f).X))
    (B : ClosedSubspace V.X)
    [IsQuasiCompact A.X] [IsAbsolutelyQuasiSeparated A.X]
    [IsQuasiCompact B.X] [IsAbsolutelyQuasiSeparated B.X]
    (φ : A.X ⟶ B.X) [IsIso φ]
    (h_restrict : φ ≫ B.ι = A.ι ≫ restrictTo f V)
    (h_etale : ∀ a : Points A.X,
      EtaleAt f (Points.map (A.ι ≫ (V.inverseImage f).ι) a)),
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y) (Z : ClosedSubspace Y)
      (h_blowup : IsBlowup b Z) (h_fp : FinitePresentation Z.ι)
      (h_disjoint : Disjoint Z.pointsSet V.pointsSet)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι),
      let E := Z.inverseImageSubspace b
      ∀ (abar : GeometricPoint (strictTransform b E f).X),
        abar.image ∈
            closure
              (Points.map (strictTransformFst b E f) ⁻¹'
                Set.range (Points.map (A.ι ≫ (V.inverseImage f).ι))) →
          ∃ (I : Ideal (etaleLocalRing (strictTransform b E f).X abar)),
            let g := (Ideal.Quotient.mk I).comp
              (etaleLocalRingMap (strictTransformSnd b E f) abar)
            I ≠ ⊤ ∧ IsLocalHom g ∧ RingHom.Finite g ∧ RingHom.Flat g
  )

end StrictTransform

end AlgebraicGeometry.AlgebraicSpace
