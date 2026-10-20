/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for associated module sheaves

Pulling an associated module sheaf back along a morphism of ringed spaces amounts to extending
its scalars along the induced map on global sections.  The primary API is functorial; objectwise
isomorphisms are exposed as its components.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X Y : RingedSpace.{u}} {R : Type u} [CommRing R]

namespace BaseChange

/-- The scalar map induced by `g : Y ⟶ X` after a chosen map into `Γ(X, O_X)`. -/
@[stacks 01BJ "base-change scalar map"]
noncomputable abbrev hom (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing) :
    R →+* Y.globalSectionsRing :=
  ((SheafedSpace.Γ.map g.op).hom).comp alpha

/-- Extension of scalars along the global-sections map induced by `g`. -/
@[stacks 01BJ "base-change module functor"]
noncomputable abbrev functor (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} Y.globalSectionsRing :=
  ModuleCat.extendScalars (hom g alpha)

/-- The module obtained by extending scalars along the global-sections map induced by `g`. -/
@[stacks 01BJ "base-change module"]
noncomputable abbrev obj (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) : ModuleCat.{u} Y.globalSectionsRing :=
  (functor g alpha).obj M

end BaseChange

/-- The map to the coefficient-ring point classified after pullback is the composite of the
original classified map with the morphism of ringed spaces. -/
@[stacks 01BJ "classified point map composition"]
theorem pointMap_comp (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing) :
    g ≫ pointMap alpha =
      pointMap (BaseChange.hom g alpha) := sorry

namespace functor

/-- Pullback of the associated-module functor is the associated-module functor for the composite
map from the coefficient ring to global sections. -/
@[stacks 01BJ "pullback comparison"]
noncomputable def pullbackIso (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing) :
    Associated.functor alpha ⋙ RingedSpace.Hom.pullback g ≅
      Associated.functor (BaseChange.hom g alpha) :=
  Functor.associator (RingedPoint.Module.functor R)
      (RingedSpace.Hom.pullback (pointMap alpha))
      (RingedSpace.Hom.pullback g) ≪≫
    Functor.isoWhiskerLeft (RingedPoint.Module.functor R)
      (RingedSpace.Hom.pullbackCompIso g (pointMap alpha)).symm ≪≫
    eqToIso (congrArg
      (fun f : Y ⟶ RingedPoint.of R ↦
        RingedPoint.Module.functor R ⋙ RingedSpace.Hom.pullback f)
      (pointMap_comp g alpha))

/-- Associating a sheaf through `alpha` is naturally isomorphic to first extending scalars along
`alpha` and then using the identity map of the global-sections ring. -/
@[stacks 01BJ "scalar extension comparison"]
noncomputable def extendScalarsIso (alpha : R →+* X.globalSectionsRing) :
    Associated.functor alpha ≅
      ModuleCat.extendScalars alpha ⋙
        Associated.functor (RingHom.id X.globalSectionsRing) :=
  Adjunction.leftAdjointUniq (adjunction alpha)
    ((ModuleCat.extendRestrictScalarsAdj alpha).comp (idAdjunction X))

/-- Pullback of associated module sheaves is naturally extension of scalars along the composite
map into global sections of the source. -/
@[stacks 01BJ "functor base change"]
noncomputable def baseChangeIso (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing) :
    Associated.functor alpha ⋙ RingedSpace.Hom.pullback g ≅
      BaseChange.functor g alpha ⋙
        Associated.functor (RingHom.id Y.globalSectionsRing) :=
  pullbackIso g alpha ≪≫
    extendScalarsIso (BaseChange.hom g alpha)

end functor

namespace obj

/-- Objectwise form of `functor.pullbackIso`. -/
noncomputable abbrev pullbackIso (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    (RingedSpace.Hom.pullback g).obj (Associated.obj alpha M) ≅
      Associated.obj (BaseChange.hom g alpha) M :=
  (functor.pullbackIso g alpha).app M

/-- Objectwise form of `functor.extendScalarsIso`. -/
noncomputable abbrev extendScalarsIso (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    Associated.obj alpha M ≅
      Associated.obj (X := X) (RingHom.id X.globalSectionsRing)
        ((ModuleCat.extendScalars alpha).obj M) :=
  (functor.extendScalarsIso alpha).app M

/-- Lemma 17.10.7 (01BJ), in functorial generality: pulling an associated module sheaf back
along `g` is canonically the identity-associated sheaf of the scalar extension along
`BaseChange.hom g alpha`. -/
@[stacks 01BJ "object base change"]
noncomputable abbrev baseChangeIso (g : Y ⟶ X) (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    (RingedSpace.Hom.pullback g).obj (Associated.obj alpha M) ≅
      Associated.obj (X := Y) (RingHom.id Y.globalSectionsRing)
        (BaseChange.obj g alpha M) :=
  (functor.baseChangeIso g alpha).app M

end obj

end AlgebraicGeometry.RingedSpace.Module.Associated
