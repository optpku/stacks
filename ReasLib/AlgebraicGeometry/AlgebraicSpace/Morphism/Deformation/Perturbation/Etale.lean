/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Etale.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Equality

/-!
# Étale pullback of perturbations of algebraic-space morphisms

The étale comparison identifies pulled-back relative differentials. Transporting
a differential-to-conormal map along this identification preserves commutative
squares of perturbed morphisms of first-order thickenings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}}

/-- The canonical identification `a₂^* Ω_{X₂/B₂} ≅ h^* a₁^* Ω_{X₁/B₁}` obtained by
inverting the étale comparison and applying pullback coherence. -/
def pullbackDifferentialsIso {B1 B2 T1 T2 X1 X2 : AlgebraicSpace S}
    (sB : B2 ⟶ B1) (f : X2 ⟶ X1) (h : T2 ⟶ T1)
    (a1 : T1 ⟶ X1) (a2 : T2 ⟶ X2) (sX1 : X1 ⟶ B1) (sX2 : X2 ⟶ B2)
    (sq : CommSq f sX2 sX1 sB) (sqA : CommSq a2 h f a1)
    [Etale f] [Etale sB] :
    (Modules.pullback a2).obj (relativeDifferentials sX2) ≅
      (Modules.pullback h).obj ((Modules.pullback a1).obj (relativeDifferentials sX1)) :=
  (Modules.pullback a2).mapIso
      (asIso (Hom.Differentials.comparison f sB sX1 sX2 sq.w)).symm ≪≫
    (Modules.pullbackCompIso a2 f).app (relativeDifferentials sX1) ≪≫
    (Modules.pullbackCongr sqA.w).app (relativeDifferentials sX1) ≪≫
    ((Modules.pullbackCompIso h a1).app (relativeDifferentials sX1)).symm

/-- The morphism of the canonical pullback-differentials identification is the composite of
the inverse étale comparison and the pullback coherence maps. -/
theorem pullbackDifferentialsIso_hom {B1 B2 T1 T2 X1 X2 : AlgebraicSpace S}
    (sB : B2 ⟶ B1) (f : X2 ⟶ X1) (h : T2 ⟶ T1)
    (a1 : T1 ⟶ X1) (a2 : T2 ⟶ X2) (sX1 : X1 ⟶ B1) (sX2 : X2 ⟶ B2)
    (sq : CommSq f sX2 sX1 sB) (sqA : CommSq a2 h f a1)
    [Etale f] [Etale sB] :
    (pullbackDifferentialsIso sB f h a1 a2 sX1 sX2 sq sqA).hom =
      (Modules.pullback a2).map
          (asIso (Hom.Differentials.comparison f sB sX1 sX2 sq.w)).inv ≫
        (Modules.pullbackCompIso a2 f).hom.app (relativeDifferentials sX1) ≫
        (Modules.pullbackCongr sqA.w).hom.app (relativeDifferentials sX1) ≫
        (Modules.pullbackCompIso h a1).inv.app (relativeDifferentials sX1) := sorry

/-- The pullback of a perturbation map through an étale square of relative differentials and
a square of conormal sheaves. -/
def pullbackPerturbationMap {B1 B2 T1 T1' T2 T2' X1 X2 : AlgebraicSpace S}
    (sB : B2 ⟶ B1) (f : X2 ⟶ X1) (h : T2 ⟶ T1)
    (a1 : T1 ⟶ X1) (a2 : T2 ⟶ X2) (sX1 : X1 ⟶ B1) (sX2 : X2 ⟶ B2)
    (iT1 : T1 ⟶ T1') (iT2 : T2 ⟶ T2') (h' : T2' ⟶ T1')
    (sq : CommSq f sX2 sX1 sB) (sqA : CommSq a2 h f a1)
    (sqT : CommSq h iT2 iT1 h')
    [Etale f] [Etale sB] [IsFirstOrderThickening iT1] [IsFirstOrderThickening iT2]
    (θ1 : (Modules.pullback a1).obj (relativeDifferentials sX1) ⟶ Hom.conormalSheaf iT1) :
    (Modules.pullback a2).obj (relativeDifferentials sX2) ⟶ Hom.conormalSheaf iT2 :=
  (pullbackDifferentialsIso sB f h a1 a2 sX1 sX2 sq sqA).hom ≫
    (Modules.pullback h).map θ1 ≫ Hom.Conormal.map sqT

/-- The pullback perturbation map is the differential identification followed by the pulled
map and the conormal comparison. -/
theorem pullbackPerturbationMap_def {B1 B2 T1 T1' T2 T2' X1 X2 : AlgebraicSpace S}
    (sB : B2 ⟶ B1) (f : X2 ⟶ X1) (h : T2 ⟶ T1)
    (a1 : T1 ⟶ X1) (a2 : T2 ⟶ X2) (sX1 : X1 ⟶ B1) (sX2 : X2 ⟶ B2)
    (iT1 : T1 ⟶ T1') (iT2 : T2 ⟶ T2') (h' : T2' ⟶ T1')
    (sq : CommSq f sX2 sX1 sB) (sqA : CommSq a2 h f a1)
    (sqT : CommSq h iT2 iT1 h')
    [Etale f] [Etale sB] [IsFirstOrderThickening iT1] [IsFirstOrderThickening iT2]
    (θ1 : (Modules.pullback a1).obj (relativeDifferentials sX1) ⟶ Hom.conormalSheaf iT1) :
    pullbackPerturbationMap sB f h a1 a2 sX1 sX2 iT1 iT2 h' sq sqA sqT θ1 =
      (pullbackDifferentialsIso sB f h a1 a2 sX1 sX2 sq sqA).hom ≫
        (Modules.pullback h).map θ1 ≫ Hom.Conormal.map sqT := sorry

/-- Perturbations transported through an étale square preserve the commutative square of
ambient morphisms. -/
theorem perturbation_commSq_of_etale
    {B1 B2 T1 T1' T2 T2' X1 X1' X2 X2' : AlgebraicSpace S}
    (sB : B2 ⟶ B1)
    (sX1 : X1 ⟶ B1) (sX1' : X1' ⟶ B1)
    (sX2 : X2 ⟶ B2) (sX2' : X2' ⟶ B2)
    (iT1 : T1 ⟶ T1') (iX1 : X1 ⟶ X1') (iT2 : T2 ⟶ T2') (iX2 : X2 ⟶ X2')
    (a1 : T1 ⟶ X1) (a1' : T1' ⟶ X1') (a2 : T2 ⟶ X2) (a2' : T2' ⟶ X2')
    (h : T2 ⟶ T1) (h' : T2' ⟶ T1') (f : X2 ⟶ X1) (f' : X2' ⟶ X1')
    [IsFirstOrderThickening iT1] [IsFirstOrderThickening iX1]
    [IsFirstOrderThickening iT2] [IsFirstOrderThickening iX2]
    [Etale f] [Etale sB]
    (sqA1 : CommSq a1 iT1 iX1 a1') (sqA2 : CommSq a2 iT2 iX2 a2')
    (sqT : CommSq h iT2 iT1 h') (sqX : CommSq f iX2 iX1 f')
    (sq0 : CommSq a2 h f a1) (sq1 : CommSq a2' h' f' a1')
    (sqS : CommSq f' sX2' sX1' sB)
    (hX1 : iX1 ≫ sX1' = sX1) (hX2 : iX2 ≫ sX2' = sX2)
    (θ1 : (Modules.pullback a1).obj (relativeDifferentials sX1) ⟶ Hom.conormalSheaf iT1)
    (b1' : T1' ⟶ X1') (b2' : T2' ⟶ X2')
    (hb1 : IsPerturbation sX1 (a1' ≫ sX1') sX1' iT1 iX1 a1 a1' sqA1 θ1 b1')
    (hb2 : IsPerturbation sX2 (a2' ≫ sX2') sX2' iT2 iX2 a2 a2' sqA2
      (pullbackPerturbationMap sB f h a1 a2 sX1 sX2 iT1 iT2 h'
        (by simpa only [hX1, hX2] using sqX.vert_comp sqS) sq0 sqT θ1)
      b2') :
    CommSq b2' h' f' b1' := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
