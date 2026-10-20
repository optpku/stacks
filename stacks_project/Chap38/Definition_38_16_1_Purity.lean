module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

#check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
      (s : S), Prop)

#check
  (AlgebraicGeometry.Scheme.Modules.isPureAlong_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
      (s : S), F.IsPureAlong f s ↔
        ∀ I : AlgebraicGeometry.Scheme.Modules.Impurity F f s, ¬ I.IsElementary)

#check
  (AlgebraicGeometry.Scheme.Modules.IsUniversallyPureAlong :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
      (s : S), Prop)

#check
  (AlgebraicGeometry.Scheme.Modules.isUniversallyPureAlong_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
      (s : S), F.IsUniversallyPureAlong f s ↔
        ∀ I : AlgebraicGeometry.Scheme.Modules.Impurity F f s, False)

#check
  (AlgebraicGeometry.Scheme.Modules.IsUniversallyPureOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType], Prop)

#check
  (AlgebraicGeometry.Scheme.Modules.isUniversallyPureOver_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType],
      F.IsUniversallyPureOver f ↔ ∀ s : S, F.IsUniversallyPureAlong f s)

#check
  (AlgebraicGeometry.Scheme.Modules.IsPureOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType], Prop)

#check
  (AlgebraicGeometry.Scheme.Modules.isPureOver_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType],
      F.IsPureOver f ↔ ∀ s : S, F.IsPureAlong f s)

#check
  (AlgebraicGeometry.Scheme.IsPureAlong :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] (s : S), Prop)

#check
  (AlgebraicGeometry.Scheme.isPureAlong_iff_structureSheaf :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] (s : S),
      AlgebraicGeometry.Scheme.IsPureAlong f s ↔
        AlgebraicGeometry.Scheme.Modules.IsPureAlong
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) f s)

#check
  (AlgebraicGeometry.Scheme.IsPureOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f], Prop)

#check
  (AlgebraicGeometry.Scheme.isPureOver_iff_structureSheaf :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f],
      AlgebraicGeometry.Scheme.IsPureOver f ↔
        AlgebraicGeometry.Scheme.Modules.IsPureOver
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) f)
