/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FormalGlueing.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalGlueing.BaseChange
import StacksCheckRecall

/-! # Flat base change of formal glueing of quasi-coherent modules -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing

universe u

section
open QCoh.FormalGlueing

/- Lemma 81.10.8 (1). The quasi-coherent glueing functor commutes with flat base change. -/
@[stacks 0AEZ] #check (AlgebraicGeometry.AlgebraicSpace.functorBaseChange_isIso :
  ∀ {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] [Flat g],
    IsIso (functorBaseChangeNatTrans f i g))

end

section
open Modules Modules.FormalGlueing

/- Lemma 81.10.8 (2). The reverse kernel of a quasi-coherent triple commutes with flat base change. -/
@[stacks 0AEZ] #check (AlgebraicGeometry.AlgebraicSpace.reverseBaseChange_isIso :
  ∀ {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] [Flat g] (H : (U i).Modules) (G : Y.Modules)
    (φ : (Modules.pullback (restrictF f i)).obj H ⟶ restrict G (j' f i))
    [H.IsQuasicoherent] [G.IsQuasicoherent] [IsIso φ],
    IsIso (reverseBaseChangeHom f i g H G φ))

end

section
open Modules Modules.FormalGlueing

#check AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing.reverseBaseChangeHom_naturality

end
