module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Finiteness.Projective
public import ReasLib.GroupTheory.MonoidExtension.Nat

/-!
# Restriction and linear actions for monoid-algebra modules

Scalar restriction along an extension inclusion is explicit. Restriction to subgroup
algebras and the resulting centralizer-linear action are canonical.
-/

@[expose] public section

noncomputable section

universe u v w x

open scoped MonoidAlgebra

namespace MonoidAlgebra

/-- The kernel-group action is the restriction of the monoid action along the extension inclusion. -/
class IsRestrictionAlongInl (Λ : Type u) {G : Type v} {Γ : Type w}
    [Ring Λ] [Group G] [Monoid Γ]
    (S : NatMonoidExtension G Γ) (P : Type x)
    [AddCommGroup P] [moduleGamma : Module (Λ[Γ]) P] [moduleG : Module (Λ[G]) P] : Prop where
  /-- Scalar multiplication agrees with the action pushed forward along the inclusion. -/
  smul_eq : ∀ (x : Λ[G]) (p : P), x • p = mapDomainRingHom Λ S.inl x • p

/-- Compatible scalar restriction agrees on group-algebra basis elements. -/
theorem IsRestrictionAlongInl.smul_single
    {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
    [Ring Λ] [Group G] [Monoid Γ]
    [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P]
    (S : NatMonoidExtension G Γ) [IsRestrictionAlongInl Λ S P] (g : G) (p : P) :
    (single g (1 : Λ) : Λ[G]) • p = (single (S.inl g) (1 : Λ) : Λ[Γ]) • p := sorry

variable {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
variable [Ring Λ] [Group G] [Monoid Γ]
variable [AddCommGroup P] [Module (Λ[Γ]) P]
variable (S : NatMonoidExtension G Γ)

/-- The module obtained by restricting scalars along an explicit extension inclusion. -/
@[reducible] def moduleRestrictInl : Module (Λ[G]) P :=
  Module.compHom P (mapDomainRingHom Λ S.inl)

/-- The explicitly restricted module has the canonical compatibility with its original action. -/
instance IsRestrictionAlongInl.instRestrictInl :
    IsRestrictionAlongInl Λ S P (moduleG := moduleRestrictInl S) :=
  IsRestrictionAlongInl.mk (moduleG := moduleRestrictInl S) (fun _ _ ↦ rfl)

variable [Module (Λ[G]) P]

/-- Restriction of a group-algebra module to a subgroup algebra. -/
instance moduleRestrictSubgroup (H : Subgroup G) : Module (Λ[H]) P :=
  Module.compHom P (mapDomainRingHom Λ H.subtype)

/-- Restriction to a subgroup algebra keeps the coefficient scalar tower. -/
instance isScalarTowerRestrictSubgroup (H : Subgroup G) [Module Λ P]
    [IsScalarTower Λ (Λ[G]) P] : IsScalarTower Λ (Λ[H]) P := by
  refine ⟨fun a x p => ?_⟩
  change (mapDomainRingHom Λ H.subtype (a • x)) • p =
    a • ((mapDomainRingHom Λ H.subtype x) • p)
  rw [← smul_assoc]
  congr 1
  simp [mapDomainRingHom_apply, MonoidAlgebra.mapDomain_smul]

/-- Finite generation over a finite group algebra persists on restriction to a subgroup algebra. -/
instance finiteRestrictSubgroup (H : Subgroup G) [Finite G]
    [Module.Finite (Λ[G]) P] : Module.Finite (Λ[H]) P := sorry

/-- Finite projectivity over a finite group algebra persists on restriction to a subgroup algebra. -/
instance projectiveRestrictSubgroup (H : Subgroup G) [Finite G]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P] :
    Module.Projective (Λ[H]) P := sorry

end MonoidAlgebra

namespace LinearMap.FiniteProjective

variable {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
variable [Ring Λ] [Group G] [Monoid Γ]
variable [AddCommGroup P] [Module (Λ[Γ]) P] [Module Λ P]

/-- The action of a monoid-algebra basis element preserves addition. -/
theorem smulEnd_map_add [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) (p q : P) :
    (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • (p + q) =
      (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p +
        (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • q := sorry

/-- The action of a monoid-algebra basis element commutes with coefficient scalars. -/
theorem smulEnd_map_smul [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) (a : Λ) (p : P) :
    (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • (a • p) =
      a • ((MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p) := sorry

/-- The coefficient-linear action of a monoid element on a monoid-algebra module. -/
def smulEnd [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) : Module.End Λ P where
  toFun p := (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p
  map_add' := smulEnd_map_add γ
  map_smul' := smulEnd_map_smul γ

/-- The coefficient-linear action evaluates as multiplication by the corresponding basis element. -/
theorem smulEnd_apply [IsScalarTower Λ (Λ[Γ]) P] (γ : Γ) (p : P) :
    (smulEnd γ : Module.End Λ P) p = (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p := sorry

variable [Module (Λ[G]) P]
variable (S : NatMonoidExtension G Γ)

/-- The action of a monoid element preserves addition when viewed over its centralizer algebra. -/
theorem smulEndZ_map_add [MonoidAlgebra.IsRestrictionAlongInl Λ S P]
    (γ : Γ) (p q : P) :
    (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • (p + q) =
      (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p +
        (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • q := sorry

/-- The action of a monoid element commutes with scalars from its kernel-group centralizer algebra. -/
theorem smulEndZ_map_smul [MonoidAlgebra.IsRestrictionAlongInl Λ S P]
    (γ : Γ) (a : Λ[S.centralizer γ]) (p : P) :
    (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • (a • p) =
      a • ((MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p) := sorry

/-- The centralizer-algebra-linear action of a monoid element. -/
def smulEndZ [MonoidAlgebra.IsRestrictionAlongInl Λ S P] (γ : Γ) :
    Module.End (Λ[S.centralizer γ]) P where
  toFun p := (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p
  map_add' := smulEndZ_map_add S γ
  map_smul' := smulEndZ_map_smul S γ

/-- The centralizer-linear action evaluates as multiplication by the corresponding basis element. -/
theorem smulEndZ_apply [MonoidAlgebra.IsRestrictionAlongInl Λ S P] (γ : Γ) (p : P) :
    (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) P) p =
      (MonoidAlgebra.single γ (1 : Λ) : Λ[Γ]) • p := sorry

end LinearMap.FiniteProjective
