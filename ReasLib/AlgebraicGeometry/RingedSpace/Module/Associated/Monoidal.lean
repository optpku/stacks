/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Functor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal associated module sheaves

The associated-module functor is the composite of the strong-monoidal point-module functor and
strong-monoidal pullback along the point classified by the global scalar map.  This file exposes
that composite structure and its tensor and unit isomorphisms directly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- Pullback along the point classified by `alpha` is canonically strong monoidal. -/
@[stacks 01BI "strong-monoidal pullback along the classified point", implicit_reducible]
noncomputable instance pointMapPullbackMonoidal
    (alpha : R →+* X.globalSectionsRing) :
    (RingedSpace.Hom.pullback (pointMap alpha)).Monoidal :=
  RingedSpace.Hom.pullbackMonoidal (pointMap alpha)

/-- The associated-module functor is canonically strong monoidal. -/
@[stacks 01BI "strong-monoidal associated module functor", implicit_reducible]
noncomputable instance functorMonoidal
    (alpha : R →+* X.globalSectionsRing) :
    (functor alpha).Monoidal :=
  Functor.Monoidal.instComp
    (F := RingedPoint.Module.functor R)
    (G := RingedSpace.Hom.pullback (pointMap alpha))

/-- The tensorator of the associated-module functor, bundled as a natural isomorphism. -/
@[stacks 01BI "associated-module tensor natural isomorphism"]
noncomputable abbrev tensorNatIso
    (alpha : R →+* X.globalSectionsRing) :
    Functor.prod (functor alpha) (functor alpha) ⋙
        MonoidalCategory.tensor X.Modules ≅
      MonoidalCategory.tensor (ModuleCat.{u} R) ⋙ functor alpha :=
  Functor.Monoidal.μNatIso (functor alpha)

/-- The canonical tensor-product isomorphism for associated module sheaves. -/
@[stacks 01BI "associated-module tensor product"]
noncomputable abbrev tensorIso
    (alpha : R →+* X.globalSectionsRing) (M N : ModuleCat.{u} R) :
    obj alpha M ⊗ obj alpha N ≅ obj alpha (M ⊗ N) :=
  (tensorNatIso alpha).app (M, N)

/-- The canonical tensor-unit isomorphism for associated module sheaves. -/
@[stacks 01BI "associated-module tensor unit"]
noncomputable abbrev unitIso
    (alpha : R →+* X.globalSectionsRing) :
    𝟙_ X.Modules ≅ obj alpha (𝟙_ (ModuleCat.{u} R)) :=
  Functor.Monoidal.εIso (functor alpha)

#synth (RingedSpace.Hom.pullback
  (pointMap (X := X) (RingHom.id X.globalSectionsRing))).Monoidal
#synth (functor (RingHom.id X.globalSectionsRing)).Monoidal

end AlgebraicGeometry.RingedSpace.Module.Associated
