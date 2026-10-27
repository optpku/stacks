/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic
public import Mathlib.CategoryTheory.Category.Cat

@[expose] public section

noncomputable section

open CategoryTheory DPPolynomial.DeRham
open scoped TensorProduct

universe u

namespace Connection.Adic

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} {δ : DividedPowers J} {p : ℕ}
variable {M N P Q : Type u} [AddCommGroup M] [Module (completedRingB B p) M]
variable [AddCommGroup N] [Module (completedRingB B p) N]
variable [AddCommGroup P] [Module (completedRingB B p) P]
variable [AddCommGroup Q] [Module (completedRingB B p) Q]

/-- A linear coefficient map induces a map on completed tensors with one-forms. -/
def tensorMap (f : M →ₗ[completedRingB B p] N) :=
  AdicCompletion.map (principalIdealB (completedRingB B p) p)
    (TensorProduct.map f
      (LinearMap.id : exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
        exteriorPower.completedForm B p (formB A B δ) 1))

/-- A horizontal morphism is a linear map commuting with the completed connections. -/
@[ext]
structure Hom (connM : Adic A B δ p M) (connN : Adic A B δ p N) where
  /-- The linear coefficient map. -/
  toLinearMap : M →ₗ[completedRingB B p] N
  /-- Horizontality of the coefficient map. -/
  commutes : ∀ m,
    connN.toAddMonoidHom (toLinearMap m) = tensorMap (δ := δ) toLinearMap (connM.toAddMonoidHom m)

namespace Hom

variable {connM : Adic A B δ p M} {connN : Adic A B δ p N}
variable {connP : Adic A B δ p P} {connQ : Adic A B δ p Q}

/-- Construct a horizontal morphism from a linear map and its commutation proof. -/
def of (f : M →ₗ[completedRingB B p] N)
    (hf : ∀ m, connN.toAddMonoidHom (f m) = tensorMap (δ := δ) f (connM.toAddMonoidHom m)) :
    Hom connM connN := ⟨f, hf⟩

/-- The identity coefficient map is horizontal. -/
theorem id_commutes (connM : Adic A B δ p M) (m : M) :
    connM.toAddMonoidHom m =
      tensorMap (δ := δ) (LinearMap.id : M →ₗ[completedRingB B p] M)
        (connM.toAddMonoidHom m) := sorry

/-- The identity horizontal morphism. -/
def id (connM : Adic A B δ p M) : Hom connM connM :=
  of LinearMap.id (id_commutes connM)

/-- Composing horizontal coefficient maps gives a horizontal map. -/
theorem comp_commutes (f : Hom connM connN) (g : Hom connN connP) (m : M) :
    connP.toAddMonoidHom (g.toLinearMap (f.toLinearMap m)) =
      tensorMap (δ := δ) (g.toLinearMap.comp f.toLinearMap) (connM.toAddMonoidHom m) := sorry

/-- Composition of horizontal morphisms is composition of their coefficient maps. -/
def comp (f : Hom connM connN) (g : Hom connN connP) : Hom connM connP :=
  of (g.toLinearMap.comp f.toLinearMap) (comp_commutes f g)

/-- Composing the identity on the source leaves a horizontal map unchanged. -/
theorem id_comp (f : Hom connM connN) : comp (id connM) f = f := sorry

/-- Composing the identity on the target leaves a horizontal map unchanged. -/
theorem comp_id (f : Hom connM connN) : comp f (id connN) = f := sorry

/-- Composition of horizontal morphisms is associative. -/
theorem assoc (f : Hom connM connN) (g : Hom connN connP) (h : Hom connP connQ) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

set_option backward.isDefEq.respectTransparency false in
/-- A coordinate functional contracts a tensor of coefficients and completed one-forms. -/
def contraction
    (coord : exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      completedRingB B p) :
    M ⊗[completedRingB B p] exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p] M :=
  TensorProduct.lift (((LinearMap.lsmul (completedRingB B p) M).comp coord).flip)

/-- The coordinate operator of a completed connection on a complete module. -/
def «partial» (conn : Adic A B δ p M)
    (hcomplete : IsAdicComplete (principalIdealB (completedRingB B p) p) M)
    (coord : exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      completedRingB B p) : M →+ M :=
  (LinearEquiv.ofBijective (AdicCompletion.of (principalIdealB (completedRingB B p) p) M)
      (AdicCompletion.of_bijective_iff.mpr hcomplete)).symm.toAddMonoidHom.comp
    ((AdicCompletion.map (principalIdealB (completedRingB B p) p)
      (contraction coord)).toAddMonoidHom.comp conn.toAddMonoidHom)

/-- Completing a coordinate operator recovers contraction of the completed connection. -/
theorem partial_apply (conn : Adic A B δ p M)
    (hcomplete : IsAdicComplete (principalIdealB (completedRingB B p) p) M)
    (coord : exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      completedRingB B p) (m : M) :
    AdicCompletion.of (principalIdealB (completedRingB B p) p) M
        («partial» conn hcomplete coord m) =
      AdicCompletion.map (principalIdealB (completedRingB B p) p)
        (contraction coord) (conn.toAddMonoidHom m) := sorry

/-- Coordinatewise topological quasi-nilpotence means that the iterates of each coordinate
operator vanish modulo `p` for all but finitely many iteration counts, for each element. -/
def IsTopologicallyQuasiNilpotent {ι : Type u} (conn : Adic A B δ p M)
    (hcomplete : IsAdicComplete (principalIdealB (completedRingB B p) p) M)
    (coord : ι → exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      completedRingB B p) : Prop :=
  ∀ (m : M) (i : ι), Set.Finite {k : ℕ |
    («partial» conn hcomplete (coord i))^[k] m ∉
      (principalIdealB (completedRingB B p) p • (⊤ : Submodule (completedRingB B p) M))}

/-- The category of complete integrable connections that are topologically quasi-nilpotent
in the specified coordinates; morphisms are horizontal linear maps. -/
def quasiNilpotentCategory {ι : Type u}
    (coord : ι → exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      completedRingB B p) : Cat :=
  ⟨(Σ M : ModuleCat.{u} (completedRingB B p),
      {conn : Adic A B δ p M // ∃ hcomplete : IsAdicComplete (principalIdealB (completedRingB B p) p) M,
        IsIntegrable A B δ p conn ∧ IsTopologicallyQuasiNilpotent conn hcomplete coord}),
    { Hom := fun M N ↦ Hom M.2.val N.2.val
      id := fun M ↦ Hom.id M.2.val
      comp := fun f g ↦ Hom.comp f g
      id_comp := Hom.id_comp
      comp_id := Hom.comp_id
      assoc := Hom.assoc }⟩

/-- Objects in the quasi-nilpotent connection category have complete coefficient modules,
satisfy the Leibniz identity, have zero curvature, and have coordinatewise nilpotent iterates
modulo `p`. -/
theorem quasiNilpotentCategory_spec {ι : Type u}
    (coord : ι → exteriorPower.completedForm B p (formB A B δ) 1 →ₗ[completedRingB B p]
      completedRingB B p) (V : quasiNilpotentCategory coord) :
    ∃ hcomplete : IsAdicComplete (principalIdealB (completedRingB B p) p) V.1,
      (∀ (r : completedRingB B p) (m : V.1),
        V.2.val.toAddMonoidHom (r • m) = r • V.2.val.toAddMonoidHom m +
          AdicCompletion.of (principalIdealB (completedRingB B p) p) _
            (m ⊗ₜ[completedRingB B p] completedDerivation A B δ p r)) ∧
      IsIntegrable A B δ p V.2.val ∧
      IsTopologicallyQuasiNilpotent V.2.val hcomplete coord := sorry

end Connection.Adic
