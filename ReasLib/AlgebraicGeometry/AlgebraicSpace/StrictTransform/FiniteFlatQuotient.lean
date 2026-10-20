/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Comparison

/-!
# Finite-flat quotients of étale local rings after admissible blowups
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace StrictTransform

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a proper morphism of
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
@[stacks 0F48]
theorem exists_blowup_finiteFlatStalkQuotient
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
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
      EtaleAt f (Points.map (A.ι ≫ (V.inverseImage f).ι) a)) :
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
            I ≠ ⊤ ∧ IsLocalHom g ∧ RingHom.Finite g ∧ RingHom.Flat g :=
  sorry

end StrictTransform

end AlgebraicGeometry.AlgebraicSpace
