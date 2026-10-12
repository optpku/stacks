/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Purity of modules over schemes

Purity along a fibre excludes elementary impurities, while universal purity excludes all
impurities. Relative purity requires the corresponding condition over every point of the base.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- A finite type quasicoherent module is pure along the fibre over `s` when it has no
impurity above `s` whose base change is an elementary étale neighbourhood. -/
def IsPureAlong (F : X.Modules) (f : X ⟶ S) [Scheme.Hom.FiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S) : Prop :=
  ∀ I : Impurity F f s, ¬ I.IsElementary

/-- Purity along a fibre is the absence of elementary impurities above its base point. -/
theorem isPureAlong_iff (F : X.Modules) (f : X ⟶ S) [Scheme.Hom.FiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S) :
    F.IsPureAlong f s ↔ ∀ I : Impurity F f s, ¬ I.IsElementary := sorry

/-- A finite type quasicoherent module is universally pure along the fibre over `s`
when it has no impurity above `s`. -/
def IsUniversallyPureAlong (F : X.Modules) (f : X ⟶ S) [Scheme.Hom.FiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S) : Prop :=
  IsEmpty (Impurity F f s)

/-- Universal purity along a fibre is the absence of every impurity above its base point. -/
theorem isUniversallyPureAlong_iff (F : X.Modules) (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (s : S) :
    F.IsUniversallyPureAlong f s ↔ ∀ I : Impurity F f s, False := sorry

/-- A finite type quasicoherent module is universally pure relative to `S` when it is
universally pure along every fibre of `f`. -/
def IsUniversallyPureOver (F : X.Modules) (f : X ⟶ S) [Scheme.Hom.FiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] : Prop :=
  ∀ s : S, F.IsUniversallyPureAlong f s

/-- Universal relative purity is universal purity along every fibre. -/
theorem isUniversallyPureOver_iff (F : X.Modules) (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsUniversallyPureOver f ↔ ∀ s : S, F.IsUniversallyPureAlong f s := sorry

/-- A finite type quasicoherent module is pure relative to `S` when it is pure along
every fibre of `f`. -/
def IsPureOver (F : X.Modules) (f : X ⟶ S) [Scheme.Hom.FiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] : Prop :=
  ∀ s : S, F.IsPureAlong f s

/-- Relative purity is purity along every fibre. -/
theorem isPureOver_iff (F : X.Modules) (f : X ⟶ S) [Scheme.Hom.FiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsPureOver f ↔ ∀ s : S, F.IsPureAlong f s := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- A scheme is pure along its fibre over `s` when its structure sheaf is pure there. -/
def IsPureAlong (f : X ⟶ S) [Hom.FiniteType f] (s : S) : Prop :=
  Modules.IsPureAlong (SheafOfModules.unit X.ringCatSheaf : X.Modules) f s

/-- Scheme purity along a fibre is module purity of the structure sheaf. -/
theorem isPureAlong_iff_structureSheaf (f : X ⟶ S) [Hom.FiniteType f] (s : S) :
    IsPureAlong f s ↔
      Modules.IsPureAlong (SheafOfModules.unit X.ringCatSheaf : X.Modules) f s := sorry

/-- A scheme is pure relative to `S` when its structure sheaf is pure relative to `S`. -/
def IsPureOver (f : X ⟶ S) [Hom.FiniteType f] : Prop :=
  Modules.IsPureOver (SheafOfModules.unit X.ringCatSheaf : X.Modules) f

/-- Relative purity of a scheme is relative module purity of its structure sheaf. -/
theorem isPureOver_iff_structureSheaf (f : X ⟶ S) [Hom.FiniteType f] :
    IsPureOver f ↔
      Modules.IsPureOver (SheafOfModules.unit X.ringCatSheaf : X.Modules) f := sorry

end AlgebraicGeometry.Scheme
