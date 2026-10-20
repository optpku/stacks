/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IsomFunctor

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 99.4.1: in Situation 99.3.1 the functor `Isom(F, G)` satisfies
the sheaf property for the fpqc topology. -/
@[stacks 08K8]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomFunctor_isSheaf_fpqc :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (isomFunctor f F G))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomFunctor_isSheafFor_fpqcCovering :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_cover : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U),
    Presieve.IsSheafFor (isomFunctor f F G) (Presieve.ofArrows V h))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_of_fpqcCovering :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_cover : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U)
    (u : baseChangeModule f U.hom F ⟶ baseChangeModule f U.hom G)
    (h_iso : ∀ i, IsIso (baseChangeHom f F G (h i) u)), IsIso u)

end AlgebraicGeometry.AlgebraicSpace.Modules
