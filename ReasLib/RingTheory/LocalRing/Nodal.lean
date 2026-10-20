/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import ReasLib.FieldTheory.Separable.Generated
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Conormal

@[expose] public section

noncomputable section

universe u v

open IsLocalRing Polynomial

/-- A Noetherian reduced local ring with two-dimensional cotangent space and a nondegenerate
quadratic relation is a nodal local ring. -/
class IsNodalLocalRing (A : Type u) [CommRing A] [IsLocalRing A] : Prop where
  isNoetherianRing : IsNoetherianRing A
  isReduced : IsReduced A
  cotangent_finrank : Module.finrank (ResidueField A) (CotangentSpace A) = 2
  existsPresentation :
    ∃ (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))
        (a b c : ResidueField A),
      a ≠ 0 ∧ 4 * a * c - b ^ 2 ≠ 0 ∧
        idealConormalAlgebraQuotient (maximalIdeal A)
            (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
              b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
                SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
              c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0

namespace IsNodalLocalRing

/-- A nodal local ring is Noetherian. -/
instance toIsNoetherianRing (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNodalLocalRing A] : IsNoetherianRing A :=
  IsNodalLocalRing.isNoetherianRing

/-- A nodal local ring is reduced. -/
instance toIsReduced (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNodalLocalRing A] : IsReduced A :=
  IsNodalLocalRing.isReduced

end IsNodalLocalRing

/-- The intrinsic nodal-local-ring condition in terms of the cotangent space and its
nondegenerate quadratic relation. -/
theorem isNodalLocalRing_iff (A : Type u) [CommRing A] [IsLocalRing A] :
    IsNodalLocalRing A ↔
      IsNoetherianRing A ∧ IsReduced A ∧
        Module.finrank (ResidueField A) (CotangentSpace A) = 2 ∧
          ∃ (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))
              (a b c : ResidueField A),
            a ≠ 0 ∧ 4 * a * c - b ^ 2 ≠ 0 ∧
              idealConormalAlgebraQuotient (maximalIdeal A)
                  (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
                    b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
                      SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
                    c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0 :=
  sorry

namespace NodalLocalRing

/-- The quadratic residue-field algebra canonically attached, up to algebra equivalence, to a
nodal local ring. Its representative is an `AdjoinRoot` of a valid quadratic presentation. -/
@[reducible]
noncomputable def quadraticAlgebra (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNodalLocalRing A] : Type u :=
  let h₀ := IsNodalLocalRing.existsPresentation (A := A)
  let h₁ := Classical.choose_spec h₀
  let a := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let b := Classical.choose h₂
  let h₃ := Classical.choose_spec h₂
  let c := Classical.choose h₃
  AdjoinRoot (C a * X ^ 2 + C b * X + C c)

/-- The canonical commutative-ring structure on the quadratic algebra of a nodal local ring. -/
noncomputable instance quadraticAlgebraCommRing (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNodalLocalRing A] : CommRing (quadraticAlgebra A) :=
  let h₀ := IsNodalLocalRing.existsPresentation (A := A)
  let h₁ := Classical.choose_spec h₀
  let a := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let b := Classical.choose h₂
  let h₃ := Classical.choose_spec h₂
  let c := Classical.choose h₃
  inferInstanceAs (CommRing (AdjoinRoot (C a * X ^ 2 + C b * X + C c)))

/-- The canonical residue-field algebra structure on the quadratic algebra of a nodal local ring. -/
noncomputable instance quadraticAlgebraAlgebra (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNodalLocalRing A] : Algebra (ResidueField A) (quadraticAlgebra A) :=
  let h₀ := IsNodalLocalRing.existsPresentation (A := A)
  let h₁ := Classical.choose_spec h₀
  let a := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let b := Classical.choose h₂
  let h₃ := Classical.choose_spec h₂
  let c := Classical.choose h₃
  inferInstanceAs
    (Algebra (ResidueField A) (AdjoinRoot (C a * X ^ 2 + C b * X + C c)))

/-- The quadratic algebra of a nodal local ring is finite-dimensional over its residue field. -/
instance quadraticAlgebraFiniteDimensional (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNodalLocalRing A] : FiniteDimensional (ResidueField A) (quadraticAlgebra A) := sorry

/-- The quadratic algebra of a nodal local ring is separable over its residue field. -/
instance quadraticAlgebraIsSeparable (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNodalLocalRing A] : Algebra.IsSeparable (ResidueField A) (quadraticAlgebra A) := sorry

/-- The quadratic algebra of a nodal local ring has degree two over its residue field. -/
theorem quadraticAlgebra_finrank_eq_two (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNodalLocalRing A] :
    Module.finrank (ResidueField A) (quadraticAlgebra A) = 2 := sorry

/-- The quadratic algebra admits a valid nodal quadratic presentation. -/
theorem quadraticAlgebra_existsPresentation (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNodalLocalRing A] :
    ∃ (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))
        (a b c : ResidueField A),
      a ≠ 0 ∧ 4 * a * c - b ^ 2 ≠ 0 ∧
        idealConormalAlgebraQuotient (maximalIdeal A)
            (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
              b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
                SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
              c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0 ∧
        Nonempty
          (AdjoinRoot (C a * X ^ 2 + C b * X + C c) ≃ₐ[ResidueField A]
            quadraticAlgebra A) := sorry

/-- Every valid nodal quadratic presentation gives the same quadratic algebra up to residue-field
algebra equivalence. -/
theorem quadraticAlgebra_equiv_adjoinRoot
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNodalLocalRing A]
    (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))
    (a b c : ResidueField A) (ha : a ≠ 0) (h_discriminant : 4 * a * c - b ^ 2 ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    Nonempty
      (AdjoinRoot (C a * X ^ 2 + C b * X + C c) ≃ₐ[ResidueField A]
        quadraticAlgebra A) := sorry

/-- The canonical quadratic algebra has degree two and is separable when the residue field is
separable over the base field. -/
theorem quadraticAlgebra_spec
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra k A] [IsNodalLocalRing A]
    [Algebra.IsSeparableOver k (ResidueField A)] :
    Module.finrank (ResidueField A) (quadraticAlgebra A) = 2 ∧
      Algebra.IsSeparable (ResidueField A) (quadraticAlgebra A) := sorry

/-- Every nondegenerate quadratic relation in valid cotangent coordinates presents the canonical
quadratic algebra as the corresponding quadratic `AdjoinRoot`. -/
theorem quadraticPresentation_equiv
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra k A] [IsNodalLocalRing A]
    [Algebra.IsSeparableOver k (ResidueField A)]
    (e : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))
    (a b c : ResidueField A) (ha : a ≠ 0) (h_discriminant : 4 * a * c - b ^ 2 ≠ 0)
    (h_relation :
      idealConormalAlgebraQuotient (maximalIdeal A)
          (a • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) ^ 2 +
            b • (SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 0) *
              SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1)) +
            c • SymmetricAlgebra.ι (ResidueField A) (CotangentSpace A) (e 1) ^ 2) = 0) :
    Nonempty
      (AdjoinRoot (C a * X ^ 2 + C b * X + C c) ≃ₐ[ResidueField A]
        quadraticAlgebra A) := sorry

end NodalLocalRing

namespace IsLocalRing

/-- For a Noetherian local `k`-algebra `A`, separability of its residue field,
reducedness, depth one, and a quadratic presentation of its completion are
related by the nodal local-algebra characterization. -/
theorem nodalLocalAlgebra_tfae
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] :
    let κ := ResidueField A
    let V := CotangentSpace A
    let hasQuadraticRelation :=
      ∃ (e : Module.Basis (Fin 2) κ V) (a b c : κ),
        4 * a * c - b ^ 2 ≠ 0 ∧
          idealConormalAlgebraQuotient (maximalIdeal A)
              (a • SymmetricAlgebra.ι κ V (e 0) ^ 2 +
                b • (SymmetricAlgebra.ι κ V (e 0) * SymmetricAlgebra.ι κ V (e 1)) +
                c • SymmetricAlgebra.ι κ V (e 1) ^ 2) = 0
    let reducedCondition :=
      Algebra.IsSeparableOver k κ ∧ IsReduced A ∧
        Module.finrank κ V = 2 ∧ hasQuadraticRelation
    let depthCondition :=
      Algebra.IsSeparableOver k κ ∧ moduleDepth A A = 1 ∧
        Module.finrank κ V = 2 ∧ hasQuadraticRelation
    let completionCondition :=
      Algebra.IsSeparableOver k κ ∧
        ∃ a b c : κ, 4 * a * c - b ^ 2 ≠ 0 ∧
          Nonempty
            ((MvPowerSeries (Fin 2) κ ⧸
                Ideal.span
                  {algebraMap κ (MvPowerSeries (Fin 2) κ) a *
                      MvPowerSeries.X (0 : Fin 2) ^ 2 +
                    algebraMap κ (MvPowerSeries (Fin 2) κ) b *
                      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)) +
                    algebraMap κ (MvPowerSeries (Fin 2) κ) c *
                      MvPowerSeries.X (1 : Fin 2) ^ 2}) ≃ₐ[k]
              AdicCompletion (maximalIdeal A) A)
    List.TFAE [reducedCondition, depthCondition, completionCondition] := sorry

end IsLocalRing
