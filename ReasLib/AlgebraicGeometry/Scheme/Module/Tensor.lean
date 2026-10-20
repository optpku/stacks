/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties

/-!
# Tensor closure for scheme modules

Tensor products preserve quasi-coherence and finite type for scheme modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The tensor product of quasi-coherent scheme modules is quasi-coherent. -/
instance instIsQuasicoherent_tensor {X : Scheme.{u}} {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (F ⊗ G).IsQuasicoherent :=
  SheafOfModules.IsQuasicoherent.tensor F G

/-- The tensor product of finite-type scheme modules is of finite type. -/
instance instIsFiniteType_tensor {X : Scheme.{u}} {F G : X.Modules}
    [F.IsFiniteType] [G.IsFiniteType] :
    (F ⊗ G).IsFiniteType :=
  SheafOfModules.IsFiniteType.tensor F G

end AlgebraicGeometry.Scheme.Modules
