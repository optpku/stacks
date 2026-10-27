/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Rational
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk
import StacksCheckRecall

/-!
# Rational ℓ-adic sheaves

The operator-authorized correction to Definition 64.18.6 omits the false
parenthetical “(right adjoint to the inclusion)” after “the quotient functor”.
There is no inclusion of rational ℓ-adic sheaves into integral ℓ-adic sheaves.
The Serre quotient, its rationalized morphisms, and its stalks are retained.
The left-tensor formulas below agree with the source's right-tensor formulas
by tensor-product symmetry over the commutative ring of ℓ-adic integers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Etale
open scoped ChangeOfRings TensorProduct

universe u

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- Definition 64.18.6: torsion means that one power of ℓ annihilates the sheaf. -/
@[stacks 03UR] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.IsTorsion :
    ZEllSheaf X ℓ → Prop)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.isTorsion_iff :
    ∀ (F : ZEllSheaf X ℓ),
      F.IsTorsion ↔ ∃ n : ℕ, ∀ k : ℕ, (ℓ ^ n) • 𝟙 (F.stage k) = 0)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.instIsSerreClass_torsion :
    (ZEllSheaf.torsion : ObjectProperty (ZEllSheaf X ℓ)).IsSerreClass)

/- Rational sheaves retain integral representatives and extend the Hom modules. -/
#check (AlgebraicGeometry.Scheme.Etale.QEllSheaf X ℓ : Type (u + 1))
#check (AlgebraicGeometry.Scheme.Etale.QEllSheaf.toZEllSheaf :
    QEllSheaf X ℓ → ZEllSheaf X ℓ)
#check (AlgebraicGeometry.Scheme.Etale.QEllSheaf.ofZEllSheaf :
    ZEllSheaf X ℓ → QEllSheaf X ℓ)
#check (AlgebraicGeometry.Scheme.Etale.QEllSheaf.instCategory :
    Category (QEllSheaf X ℓ))
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.qellHom_eq :
    ∀ (F G : ZEllSheaf X ℓ),
      ZEllSheaf.qellHom F G =
        (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
          (ModuleCat.of ℤ_[ℓ] (F ⟶ G)))
#check (AlgebraicGeometry.Scheme.Etale.QEllSheaf.id_eq :
    ∀ (F : QEllSheaf X ℓ),
      𝟙 F = ZEllSheaf.tensorQEll (𝟙 (QEllSheaf.toZEllSheaf F)))
#check (AlgebraicGeometry.Scheme.Etale.QEllSheaf.comp_tmul :
    ∀ {F G H : QEllSheaf X ℓ} (a b : ℚ_[ℓ])
      (f : QEllSheaf.toZEllSheaf F ⟶ QEllSheaf.toZEllSheaf G)
      (g : QEllSheaf.toZEllSheaf G ⟶ QEllSheaf.toZEllSheaf H),
      ((a ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] f : F ⟶ G) ≫
          (b ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] g : G ⟶ H) : F ⟶ H) =
        (a * b) ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] (f ≫ g))

/- The concrete quotient functor is additive and realizes the Serre localization. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.tensorQEllFunctor :
    ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ)
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.tensorQEllFunctor_obj :
    ∀ (F : ZEllSheaf X ℓ),
      (ZEllSheaf.tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ).obj F =
        QEllSheaf.ofZEllSheaf F)
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.tensorQEllFunctor_map :
    ∀ {F G : ZEllSheaf X ℓ} (f : F ⟶ G),
      (ZEllSheaf.tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ).map f =
        ZEllSheaf.tensorQEll f)
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.tensorQEllFunctor_additive :
    (ZEllSheaf.tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ).Additive)
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.tensorQEllFunctor_isLocalization :
    (ZEllSheaf.tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ).IsLocalization
      (ZEllSheaf.torsion : ObjectProperty (ZEllSheaf X ℓ)).isoModSerre)
#check (AlgebraicGeometry.Scheme.Etale.QEllSheaf.instAbelian :
    Abelian (QEllSheaf X ℓ))

/- The rational geometric stalk is scalar extension of the integral inverse limit. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk_eq :
    ∀ (F : ZEllSheaf X ℓ) (x : Scheme.GeometricPoint X),
      F.stalk x = Limits.limit (F.componentStalkSystem x))
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.qellStalk :
    ZEllSheaf X ℓ → Scheme.GeometricPoint X → ModuleCat.{u} ℚ_[ℓ])
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.qellStalk_eq :
    ∀ (F : ZEllSheaf X ℓ) (x : Scheme.GeometricPoint X),
      F.qellStalk x =
        (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
          (ModuleCat.of ℤ_[ℓ] (F.stalk x)))
