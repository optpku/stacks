/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Algebra
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Piece

/-! # Degree pieces of the conormal algebra of an immersion

The degree pieces are pullbacks of successive quotients of the coborder ideal.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.coborderIdealPower :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    IdealSubobject (Hom.coborder i))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.coborderIdealPower_eq :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    coborderIdealPower i n =
      Modules.idealPowerProductSubobject
        (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (SheafOfModules.unit (structureSheaf (Hom.coborder i))) n)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.coborderIdealPower_one :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    coborderIdealPower i 1 =
      Hom.idealSheafSubobject (IsImmersion.liftCoborder i))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.coborderQuotient :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    (Hom.coborder i).Modules)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.coborderQuotient_eq :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    coborderQuotient i n =
      Modules.quotientByIdeal
        (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (coborderIdealPower i n).toModule)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.piece :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    Z.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.piece_eq :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    piece i n =
      (Modules.pullback (IsImmersion.liftCoborder i)).obj (coborderQuotient i n))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.piecePushforwardComparison :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    coborderQuotient i n ⟶
      (Modules.pushforward (IsImmersion.liftCoborder i)).obj (piece i n))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.piecePushforwardComparison_eq :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    piecePushforwardComparison i n =
      (Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).unit.app
        (coborderQuotient i n))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.piece_spec :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    piece i n =
        (Modules.pullback (IsImmersion.liftCoborder i)).obj (coborderQuotient i n) ∧
      coborderQuotient i n =
        Modules.quotientByIdeal
          (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
          (coborderIdealPower i n).toModule ∧
      IsClosedImmersion (IsImmersion.liftCoborder i))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.instIsQuasicoherent_coborderQuotient :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    (coborderQuotient i n).IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.instIsQuasicoherent_piece :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] (n : ℕ),
    (piece i n).IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.coborderQuotient_one :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    coborderQuotient i 1 =
      Modules.quotientByIdeal
        (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i)))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.piece_one :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    piece i 1 = Hom.conormalSheaf i)

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.pieceZeroComparison :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    piece i 0 ⟶ SheafOfModules.unit (structureSheaf Z))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.pieceZeroComparison_eq :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    pieceZeroComparison i =
      (Modules.pullback (IsImmersion.liftCoborder i)).map
          (Modules.quotientByIdealComparison (IsImmersion.liftCoborder i)
            (coborderIdealPower i 0).toModule) ≫
        (Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).counit.app
          ((Modules.pullback (IsImmersion.liftCoborder i)).obj
            (coborderIdealPower i 0).toModule) ≫
        IdealSubobject.pullbackMap (coborderIdealPower i 0)
          (IsImmersion.liftCoborder i))

#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.piece_zero :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    IsIso (pieceZeroComparison i))

