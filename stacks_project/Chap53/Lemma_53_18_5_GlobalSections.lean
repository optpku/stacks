/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Field

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Compatibility definition for the explicit global-sections field construction. -/
@[implicit_reducible]
noncomputable def instFieldGlobalSectionsAlg
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [UniversallyClosed f] :
    Field (globalSectionsAlg f) :=
  globalSectionsField f

#check
  (AlgebraicGeometry.Scheme.Hom.globalSectionsField :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [UniversallyClosed f],
      Field (globalSectionsAlg f))

#check
  (AlgebraicGeometry.Scheme.Hom.globalSectionsAlgebra :
    ∀ {k : Type u} [CommRing k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      Algebra k (Scheme.globalSectionsRing X))

end AlgebraicGeometry.Scheme.Hom
