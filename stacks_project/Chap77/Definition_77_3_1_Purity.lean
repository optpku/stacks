module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap77.Definition_77_2_2_Impurity
public import stacks_project.Chap77.Lemma_77_2_5

/-!
# Purity of modules on algebraic spaces

Purity above a point excludes étale-neighbourhood impurities, while universal purity
excludes every impurity. Relative purity requires the corresponding condition over
every point of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A finite type quasi-coherent module is pure above `y` when it has no étale-neighbourhood
impurity above `y`. -/
def IsPureAlong (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) : Prop :=
  ∀ I : Impurity F f y, ¬ AlgebraicSpace.Etale I.g

/-- Purity above `y` is the absence of étale-neighbourhood impurities of `F` above `y`. -/
theorem isPureAlong_iff (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsPureAlong f y ↔ ∀ I : Impurity F f y, ¬ AlgebraicSpace.Etale I.g :=
  sorry

/-- Purity above `y` is equivalent to the non-existence of an étale-neighbourhood impurity. -/
theorem isPureAlong_iff_not_exists_etaleNeighbourhood (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsPureAlong f y ↔ ¬ Impurity.exists_etaleNeighbourhood F f y :=
  sorry

/-- Purity above `y` is equivalent to the non-existence of an impurity that is quasi-finite
at the special point. -/
theorem isPureAlong_iff_not_exists_quasiFiniteAt (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsPureAlong f y ↔ ¬ Impurity.exists_quasiFiniteAt F f y :=
  sorry

/-- Purity above `y` is equivalent to the non-existence of an impurity over a strict
henselization at a geometric point lying over `y`. -/
theorem isPureAlong_iff_not_exists_strictHenselization (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y)
    (ybar : GeometricPoint Y) (hy : ybar.liesOver y) :
    F.IsPureAlong f y ↔ ¬ Impurity.exists_strictHenselization F f y ybar :=
  sorry

/-- A finite type quasi-coherent module is universally pure above `y` when it has no
impurity above `y`. -/
def IsUniversallyPureAlong (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) : Prop :=
  IsEmpty (Impurity F f y)

/-- Universal purity above `y` is the absence of every impurity of `F` above `y`. -/
theorem isUniversallyPureAlong_iff (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] (y : Points Y) :
    F.IsUniversallyPureAlong f y ↔ ∀ I : Impurity F f y, False :=
  sorry

/-- A finite type quasi-coherent module is pure relative to `Y` when it is pure above
every point of `Y`. -/
def IsPureOver (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] : Prop :=
  ∀ y : Points Y, F.IsPureAlong f y

/-- Relative purity is purity above every point of the base. -/
theorem isPureOver_iff (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsPureOver f ↔ ∀ y : Points Y, F.IsPureAlong f y :=
  sorry

/-- A finite type quasi-coherent module is universally pure relative to `Y` when it is
universally pure above every point of `Y`. -/
def IsUniversallyPureOver (F : X.Modules) (f : X ⟶ Y) [FiniteType f] [Decent f]
    [F.IsQuasicoherent] [F.IsFiniteType] : Prop :=
  ∀ y : Points Y, F.IsUniversallyPureAlong f y

/-- Universal relative purity is universal purity above every point of the base. -/
theorem isUniversallyPureOver_iff (F : X.Modules) (f : X ⟶ Y)
    [FiniteType f] [Decent f] [F.IsQuasicoherent] [F.IsFiniteType] :
    F.IsUniversallyPureOver f ↔ ∀ y : Points Y, F.IsUniversallyPureAlong f y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The structure sheaf of an algebraic space, viewed as a module over itself, is
quasi-coherent. -/
instance instIsQuasicoherent_unit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsQuasicoherent :=
  sorry

/-- The structure sheaf of an algebraic space, viewed as a module over itself, is of
finite type. -/
instance instIsFiniteType_unit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsFiniteType :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- An algebraic space is pure above `y` when its structure sheaf is pure above `y`. -/
def IsPureAlong (f : X ⟶ Y) [FiniteType f] [Decent f] (y : Points Y) : Prop :=
  Modules.IsPureAlong (SheafOfModules.unit (structureSheaf X) : X.Modules) f y

/-- Purity of an algebraic space above `y` is module purity of its structure sheaf. -/
theorem isPureAlong_iff_structureSheaf (f : X ⟶ Y) [FiniteType f] [Decent f]
    (y : Points Y) :
    IsPureAlong f y ↔
      Modules.IsPureAlong (SheafOfModules.unit (structureSheaf X) : X.Modules) f y :=
  sorry

/-- An algebraic space is pure relative to `Y` when its structure sheaf is pure relative
to `Y`. -/
def IsPureOver (f : X ⟶ Y) [FiniteType f] [Decent f] : Prop :=
  Modules.IsPureOver (SheafOfModules.unit (structureSheaf X) : X.Modules) f

/-- Relative purity of an algebraic space is relative module purity of its structure sheaf. -/
theorem isPureOver_iff_structureSheaf (f : X ⟶ Y) [FiniteType f] [Decent f] :
    IsPureOver f ↔
      Modules.IsPureOver (SheafOfModules.unit (structureSheaf X) : X.Modules) f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
