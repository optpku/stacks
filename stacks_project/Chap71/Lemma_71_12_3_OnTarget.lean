/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.OnTarget

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
open SheafOfModules.RingedSite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.domainTopInclusion :
  ∀ {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
    {πP : P ⟶ X} {πQ : Q ⟶ X}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hTop : r.domain = OpenSubspace.id Q),
    Q ⟶ r.domain.X)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.domainTopInclusion_comp_ι :
  ∀ {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
    {πP : P ⟶ X} {πQ : Q ⟶ X}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hTop : r.domain = OpenSubspace.id Q),
    domainTopInclusion r hTop ≫ r.domain.ι = 𝟙 Q)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.mapOnTarget :
  ∀ {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
    {πP : P ⟶ X} {πQ : Q ⟶ X}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hTop : r.domain = OpenSubspace.id Q),
    Q ⟶ P)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.thetaOnTarget :
  ∀ {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
    {πP : P ⟶ X} {πQ : Q ⟶ X}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hTop : r.domain = OpenSubspace.id Q)
    (hι : domainTopInclusion r hTop ≫ r.domain.ι = 𝟙 Q)
    (n : ℤ),
    (Modules.pullback (mapOnTarget r hTop)).obj (twistP n) ⟶ twistQ n)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.mapOfFullDomain :
  ∀ {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
    {πP : P ⟶ X} {πQ : Q ⟶ X}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hFull : IsIso r.domain.ι),
    Q ⟶ P)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProjMap.thetaOfFullDomain :
  ∀ {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
    {πP : P ⟶ X} {πQ : Q ⟶ X}
    {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
    {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
    {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}
    (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    (hFull : IsIso r.domain.ι)
    (n : ℤ),
    (Modules.pullback (mapOfFullDomain r hFull)).obj (twistP n) ⟶ twistQ n)
