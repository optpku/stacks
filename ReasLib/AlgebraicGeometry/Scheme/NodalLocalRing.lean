/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.LocalRing.Nodal.TangentCone

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

namespace NodalLocalRing

/-- For a Nagata nodal local ring, the canonical quadratic algebra is the closed fiber of the
normalization. -/
theorem normalizationFiber_equiv
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    Nonempty
      (NodalLocalRing.quadraticAlgebra A ≃ₐ[ResidueField A]
        (maximalIdeal A).Fiber (Normalization.normalizationRing A)) := sorry

/-- If the leading coefficient of a nodal quadratic relation is nonzero, its second
cotangent coordinate is nonzero everywhere on the projectivized tangent cone. -/
theorem tangentChart_basicOpen_eq_top
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNodalLocalRing A]
    (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))
    (a b c : ResidueField A) (ha : a ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    Proj.basicOpen (Ideal.AssociatedGraded.grade (maximalIdeal A))
      (tangentCoordinate A e 1).1 = ⊤ := sorry

/-- A nodal quadratic presentation identifies the projectivized tangent cone with the spectrum
of its quadratic root algebra, using the ratio of the cotangent coordinates. -/
def quadraticPresentationProjIso
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNodalLocalRing A]
    (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))
    (a b c : ResidueField A) (ha : a ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    Proj (Ideal.AssociatedGraded.grade (maximalIdeal A)) ≅
      Spec (CommRingCat.of (AdjoinRoot (C a * X ^ 2 + C b * X + C c))) :=
  (Scheme.topIso _).symm ≪≫
    (Scheme.isoOfEq _ (tangentChart_basicOpen_eq_top A e a b c ha h_relation).symm) ≪≫
    Proj.basicOpenIsoSpec (Ideal.AssociatedGraded.grade (maximalIdeal A))
      (tangentCoordinate A e 1).1 (tangentCoordinate A e 1).2 (by decide : 0 < 1) ≪≫
    Scheme.Spec.mapIso
      (quadraticPresentationTangentChartEquiv A e a b c ha h_relation).toRingEquiv.toCommRingCatIso.op

/-- For a complete nodal local ring, the projectivized tangent cone is the spectrum of the
canonical quadratic algebra. -/
def associatedGradedProj_iso
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsCompleteLocalRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    Proj (Ideal.AssociatedGraded.grade (maximalIdeal A)) ≅
      Spec (CommRingCat.of (NodalLocalRing.quadraticAlgebra A)) :=
  let h₀ := IsNodalLocalRing.existsPresentation (A := A)
  let e := Classical.choose h₀
  let h₁ := Classical.choose_spec h₀
  let a := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let b := Classical.choose h₂
  let h₃ := Classical.choose_spec h₂
  let c := Classical.choose h₃
  let h := Classical.choose_spec h₃
  quadraticPresentationProjIso A e a b c h.1 h.2.2

/-- For a locally Noetherian scheme over a field, the normalization fiber at a nodal point is the
spectrum of the canonical quadratic algebra of the stalk. -/
theorem normalizationFiber_iso_specQuadraticAlgebra
    {k : Type u} [Field k] (X : SchemeOverField k) [IsLocallyNoetherian X.left]
    (x : X.left) [IsNodalLocalRing (stalkRing X x)]
    [Algebra.IsSeparableOver k (ResidueField (stalkRing X x))] :
    Nonempty
      (Spec (CommRingCat.of (NodalLocalRing.quadraticAlgebra (stalkRing X x))) ≅
        Scheme.Hom.fiber (Scheme.normalizationTo X.left) x) := sorry

end NodalLocalRing
