/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.Pushforward

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

namespace ModuleCat

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- The descent pushforward functor along a homomorphism of commutative rings. -/
#check (ModuleCat.descentPushforward :
  (f : R →+* S) →
    (extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra ⥤ ModuleCat.{max w v} R)

/- The object part of descent pushforward is the defining equalizer. -/
#check (ModuleCat.descentPushforward_obj :
  (f : R →+* S) → (D : (extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra) →
    (descentPushforward f).obj D =
      equalizer ((restrictScalars f).map D.a)
        ((extendRestrictScalarsAdj f).unit.app ((restrictScalars f).obj D.A)))

/- Descent pushforward maps commute with the canonical equalizer inclusions. -/
#check (ModuleCat.descentPushforward_map_ι :
  (f : R →+* S) → {D E : (extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra} →
    (g : D ⟶ E) →
      (descentPushforward f).map g ≫
          equalizer.ι ((restrictScalars f).map E.a)
            ((extendRestrictScalarsAdj f).unit.app ((restrictScalars f).obj E.A)) =
        equalizer.ι ((restrictScalars f).map D.a)
            ((extendRestrictScalarsAdj f).unit.app ((restrictScalars f).obj D.A)) ≫
          (restrictScalars f).map g.f)

end ModuleCat
