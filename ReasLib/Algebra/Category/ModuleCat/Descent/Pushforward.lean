/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Descent

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

namespace ModuleCat

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The descent pushforward along a ring homomorphism, realized as the right adjoint
to the comonad comparison functor for extension and restriction of scalars. -/
noncomputable def descentPushforward (f : R →+* S) :
    (extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra ⥤ ModuleCat.{max w v} R :=
  Comonad.ComonadicityInternal.rightAdjointComparison (extendRestrictScalarsAdj.{w} f)

/-- The module underlying the descent pushforward is the equalizer of the
restricted coaction and the unit of extension-restriction of scalars. -/
theorem descentPushforward_obj (f : R →+* S)
    (D : (extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra) :
    (descentPushforward f).obj D =
      equalizer ((restrictScalars f).map D.a)
        ((extendRestrictScalarsAdj f).unit.app ((restrictScalars f).obj D.A)) := sorry

/-- Descent pushforward maps commute with the canonical equalizer inclusions. -/
theorem descentPushforward_map_ι (f : R →+* S)
    {D E : (extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra} (g : D ⟶ E) :
    (descentPushforward f).map g ≫
        equalizer.ι ((restrictScalars f).map E.a)
          ((extendRestrictScalarsAdj f).unit.app ((restrictScalars f).obj E.A)) =
      equalizer.ι ((restrictScalars f).map D.a)
          ((extendRestrictScalarsAdj f).unit.app ((restrictScalars f).obj D.A)) ≫
        (restrictScalars f).map g.f := sorry

end ModuleCat

namespace ModuleCat.DescentPushforward

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The equalizer fork of a descent coaction and the adjunction unit. -/
noncomputable def fork (f : R →+* S)
    (D : (ModuleCat.extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra) :
    Fork ((ModuleCat.restrictScalars f).map D.a)
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app
        ((ModuleCat.restrictScalars f).obj D.A)) :=
  Fork.ofι
    (equalizer.ι ((ModuleCat.restrictScalars f).map D.a)
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app
        ((ModuleCat.restrictScalars f).obj D.A)))
    (equalizer.condition ((ModuleCat.restrictScalars f).map D.a)
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app
        ((ModuleCat.restrictScalars f).obj D.A)))

/-- The scalar-extension image of the equalizer fork associated to a descent coaction. -/
noncomputable def baseChangeFork (f : R →+* S)
    (D : (ModuleCat.extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra) :
    Fork ((ModuleCat.extendScalars f).map ((ModuleCat.restrictScalars f).map D.a))
      ((ModuleCat.extendScalars f).map
        ((ModuleCat.extendRestrictScalarsAdj f).unit.app
          ((ModuleCat.restrictScalars f).obj D.A))) :=
  Fork.ofCone ((ModuleCat.extendScalars f).mapCone (fork f D))

/-- The equalizer fork of a descent coaction and the adjunction unit is limiting. -/
noncomputable def forkIsLimit (f : R →+* S)
    (D : (ModuleCat.extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra) :
    IsLimit (fork f D) :=
  equalizerIsEqualizer ((ModuleCat.restrictScalars f).map D.a)
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app
      ((ModuleCat.restrictScalars f).obj D.A))

end ModuleCat.DescentPushforward
