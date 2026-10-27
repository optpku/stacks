/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k] (X : SchemeOverField k) (Λ : Type u) [Ring Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]

variable {P Q : Of (Spec (CommRingCat.of k)) X} (φ : P ⟶ Q)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [hX : HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [hP : HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Q.obj.right.left.Etale,
  HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [hQ : HasDerivedCategory
  (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : (Spec (CommRingCat.of k)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of k)).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [hP_kanModule : ∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [hQ_kanModule : ∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose Q.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Q.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [hP_kanAdd : ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [hQ_kanAdd : ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [hP_preservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
variable [hQ_preservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι Q)).op]
variable [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]


variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
    (ModuleCat.{u} Λ)).obj
    (Opposite.op (globalEtale (Spec (CommRingCat.of k))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of k)).smallEtaleTopology
        (ModuleCat.{u} Λ)).obj
      (Opposite.op (globalEtale (Spec (CommRingCat.of k))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [CompactSpace (Spec (CommRingCat.of k))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of k))]

/-- A morphism of compactifications induces the contravariant transition of compact-support models. -/
@[irreducible]
def etaleDerivedGammaCompactSupportTransition :
    etaleDerivedGammaCompactSupport (Λ := Λ) Q ⟶ etaleDerivedGammaCompactSupport (Λ := Λ) P :=
  whiskerRight (etaleDerivedLowerShriek.isoOfHom X Λ φ)
    (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ)

/-- Compact-support transitions apply derived global sections to the lower-shriek transition. -/
theorem etaleDerivedGammaCompactSupportTransition_app
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedGammaCompactSupportTransition X Λ φ).app K =
      (etaleDerivedGamma (Spec (CommRingCat.of k)) Λ).map
        (etaleDerivedLowerShriek.isoOfHom_app X Λ φ K) := by
  unfold etaleDerivedGammaCompactSupportTransition etaleDerivedLowerShriek.isoOfHom_app
  rfl

end AlgebraicGeometry.Scheme.Etale

end
