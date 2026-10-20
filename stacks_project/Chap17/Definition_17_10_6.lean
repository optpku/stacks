/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Functor
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry

open RingedSpace.Module

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]
variable (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat R) (ℱ : X.Modules)
variable (MΓ : ModuleCat (X.presheaf.obj (op ⊤)))

/- Definition 17.10.6 (01BI): `Associated.obj α M` is the `O_X`-module associated to the
`R`-module `M` through `α : R →+* Γ(X, O_X)`. -/
@[stacks 01BI]
#check @RingedSpace.Module.Associated.obj

#check Associated.obj α M
#check Associated.obj (X := X) (RingHom.id X.globalSectionsRing) MΓ

#check IsIsomorphic ℱ (Associated.obj α M)
#check IsIsomorphic ℱ
  (Associated.obj (X := X) (RingHom.id X.globalSectionsRing) MΓ)

end AlgebraicGeometry
