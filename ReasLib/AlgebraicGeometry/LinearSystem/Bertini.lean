/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.LinearSystem.UniversalDivisor
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Approximation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Bertini theorems for general linear-system sections

This file records the structure morphism of divisors cut out by scalar-extended vectors,
together with Bertini theorems for their smoothness and geometric irreducibility.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.LinearSystem

variable {k : Type} [Field k]
variable {V : Type} [AddCommGroup V] [Module k V] {r : ℕ}

/-- The structural morphism to `Spec(K)` of the divisor cut out by a scalar-extended vector. -/
noncomputable def fiberDivisorToSpecOfHom
    (X : Over (Spec (CommRingCat.of k)))
    (K : Type) [Field K] [Algebra k K]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (b : Module.Basis (Fin r) k V) (v : V ⊗[k] K) :
    fiberDivisorOfHom X K L ψ b v ⟶ Spec (CommRingCat.of K) :=
  Scheme.zeroSchemeι
      ((Scheme.Modules.pullback (FieldExtension.toSource k K X.hom)).obj L)
      (baseChangeSectionOfHom X K L ψ b v) ≫
    FieldExtension.toBase k K X.hom

/-- The divisor structure morphism is the zero-scheme immersion followed by the field-extension
base projection. -/
theorem fiberDivisorToSpecOfHom_def
    (X : Over (Spec (CommRingCat.of k)))
    (K : Type) [Field K] [Algebra k K]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (b : Module.Basis (Fin r) k V) (v : V ⊗[k] K) :
    fiberDivisorToSpecOfHom X K L ψ b v =
      Scheme.zeroSchemeι
          ((Scheme.Modules.pullback (FieldExtension.toSource k K X.hom)).obj L)
          (baseChangeSectionOfHom X K L ψ b v) ≫
        FieldExtension.toBase k K X.hom :=
  rfl

/-- A linear-system divisor is smooth over its extension field for every scalar-extended
vector under consideration. -/
def fiberDivisorSmoothOverFieldOfHom
    (X : Over (Spec (CommRingCat.of k)))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (b : Module.Basis (Fin r) k V) :
    ∀ (K : Type) [Field K] [Algebra k K], V ⊗[k] K → Prop
  | K, _, _, v => Smooth (fiberDivisorToSpecOfHom X K L ψ b v)

/-- Smoothness of a linear-system divisor means smoothness of its structure morphism to the
extension field spectrum. -/
theorem fiberDivisorSmoothOverFieldOfHom_iff
    (X : Over (Spec (CommRingCat.of k)))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (b : Module.Basis (Fin r) k V)
    (K : Type) [Field K] [Algebra k K] (v : V ⊗[k] K) :
    fiberDivisorSmoothOverFieldOfHom X L ψ b K v ↔
      Smooth (fiberDivisorToSpecOfHom X K L ψ b v) :=
  Iff.rfl

/-- On a scheme smooth over a field, an immersive generating linear system cuts out smooth
divisors for general scalar-extended vectors. -/
theorem holdsForGeneralVector_fiberDivisorSmooth_of_inducesImmersion
    (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (b : Module.Basis (Fin r) k V)
    (hψ : ProjectiveSpace.VectorSpace.LinearSystem.InducesImmersion X L ψ) :
    HoldsForGeneralVector b (fiberDivisorSmoothOverFieldOfHom X L ψ b) := sorry

/-- A general member of a finite-dimensional linear system on a finite-type geometrically
irreducible scheme is geometrically irreducible when three members witness a codimension-two
component away from the first and every base-locus component has codimension at least two. -/
theorem holdsForGeneralVector_geometricallyIrreducible
    (X : Over (Spec (CommRingCat.of k))) [Scheme.Hom.FiniteType X.hom]
    [GeometricallyIrreducible X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom ℒ)
    (b : Module.Basis (Fin r) k V) :
    let H : V → Closeds X.left := fun v ↦
      (Scheme.zeroIdealSheaf ℒ (RingedSpace.sectionFromTop ℒ (ψ v))).support
    ∀ (h_component : ∃ v₁ v₂ v₃ : V, ∃ Z : IrreducibleCloseds X.left,
        Maximal (fun Y : IrreducibleCloseds X.left ↦
          (Y : Set X.left) ⊆ (H v₂ : Set X.left) ∩ (H v₃ : Set X.left)) Z ∧
          ¬(Z : Set X.left) ⊆ (H v₁ : Set X.left) ∧
          Order.coheight Z = (2 : ℕ∞))
      (h_baseLocus : Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast
        2 (⋂ v : V, (H v : Set X.left))),
      HoldsForGeneralVector b (fun K _ _ v ↦
        GeometricallyIrreducible (fiberDivisorToSpecOfHom X K ℒ ψ b v)) := sorry

end AlgebraicGeometry.LinearSystem
